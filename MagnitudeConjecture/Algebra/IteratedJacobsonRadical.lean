import MagnitudeConjecture.Algebra.JacobsonRadicalAction

/-!
# Iterated module radicals

This file packages the radical filtration of a module as actual submodules of
the original module.  The formulation is tailored to the radical-layer
argument in Auslander--Reiten, Proposition 1.1(a): a finite radical filtration
whose nonzero tops are simple is uniserial.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v w

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The `n`th term of the module radical filtration, retained as a submodule
of the original module. -/
def iteratedModuleJacobson (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    ℕ → Submodule R M
  | 0 => ⊤
  | n + 1 =>
      (Module.jacobson R (iteratedModuleJacobson R M n)).map
        (iteratedModuleJacobson R M n).subtype

@[simp]
theorem iteratedModuleJacobson_zero :
    iteratedModuleJacobson R M 0 = ⊤ := rfl

@[simp]
theorem iteratedModuleJacobson_succ (n : ℕ) :
    iteratedModuleJacobson R M (n + 1) =
      (Module.jacobson R (iteratedModuleJacobson R M n)).map
        (iteratedModuleJacobson R M n).subtype := rfl

/-- Consecutive terms of the radical filtration are nested. -/
theorem iteratedModuleJacobson_succ_le (n : ℕ) :
    iteratedModuleJacobson R M (n + 1) ≤
      iteratedModuleJacobson R M n := by
  rw [iteratedModuleJacobson_succ]
  exact Submodule.map_subtype_le _ _

/-- A linear map carries each term of the radical filtration into the
corresponding term. -/
theorem iteratedModuleJacobson_map_le
    (f : M →ₗ[R] N) (n : ℕ) :
    (iteratedModuleJacobson R M n).map f ≤
      iteratedModuleJacobson R N n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedModuleJacobson_succ, iteratedModuleJacobson_succ]
      rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      let g : iteratedModuleJacobson R M n →ₗ[R]
          iteratedModuleJacobson R N n :=
        (f.domRestrict (iteratedModuleJacobson R M n)).codRestrict
          (iteratedModuleJacobson R N n)
          (fun x ↦ ih (Submodule.mem_map_of_mem x.2))
      have hgy : g y ∈
          Module.jacobson R (iteratedModuleJacobson R N n) :=
        Module.map_jacobson_le g ⟨y, hy, rfl⟩
      exact ⟨g y, hgy, rfl⟩

/-- Each iterated radical is the corresponding power of the ring Jacobson
radical acting on the module. -/
theorem iteratedModuleJacobson_eq_ringJacobson_pow_smul_top
    [IsSemiprimaryRing R] (n : ℕ) :
    iteratedModuleJacobson R M n =
      Ring.jacobson R ^ n • (⊤ : Submodule R M) := by
  induction n with
  | zero =>
      rw [iteratedModuleJacobson_zero]
      change (⊤ : Submodule R M) = (1 : Ideal R) • ⊤
      rw [Ideal.one_eq_top, Submodule.top_smul]
  | succ n ih =>
      rw [iteratedModuleJacobson_succ,
        moduleJacobson_eq_ringJacobson_smul_top,
        Submodule.map_smul'', Submodule.map_top,
        Submodule.range_subtype, ih, ← Submodule.mul_smul]
      have hpow : Ring.jacobson R ^ (n + 1) =
          Ring.jacobson R * Ring.jacobson R ^ n :=
        Ideal.IsTwoSided.pow_succ (I := Ring.jacobson R) n
      rw [hpow]

/-- A surjective linear map carries each radical-filtration term onto the
corresponding term. -/
theorem iteratedModuleJacobson_map_eq_of_surjective
    [IsSemiprimaryRing R]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (n : ℕ) :
    (iteratedModuleJacobson R M n).map f =
      iteratedModuleJacobson R N n := by
  rw [iteratedModuleJacobson_eq_ringJacobson_pow_smul_top,
    iteratedModuleJacobson_eq_ringJacobson_pow_smul_top,
    Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr hf]

/-- If the whole image of a map lies in the target radical, the map shifts
the radical filtration by one step. -/
theorem iteratedModuleJacobson_apply_mem_succ_of_range_le_jacobson
    [IsSemiprimaryRing R]
    (f : M →ₗ[R] N)
    (hf : LinearMap.range f ≤ Module.jacobson R N)
    (n : ℕ) {x : M}
    (hx : x ∈ iteratedModuleJacobson R M n) :
    f x ∈ iteratedModuleJacobson R N (n + 1) := by
  have hxImage : f x ∈
      (Ring.jacobson R ^ n) • LinearMap.range f := by
    rw [← Submodule.map_top f, ← Submodule.map_smul'',
      ← iteratedModuleJacobson_eq_ringJacobson_pow_smul_top]
    exact Submodule.mem_map_of_mem hx
  rw [iteratedModuleJacobson_eq_ringJacobson_pow_smul_top]
  apply (Submodule.smul_mono le_rfl hf) at hxImage
  rw [moduleJacobson_eq_ringJacobson_smul_top,
    ← Submodule.mul_smul, ← Submodule.pow_succ] at hxImage
  exact hxImage

/-- Over a semiprimary ring, the radical filtration terminates. -/
theorem iteratedModuleJacobson_eventually_eq_bot
    [IsSemiprimaryRing R] :
    ∃ n : ℕ, iteratedModuleJacobson R M n = ⊥ := by
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := R)
  refine ⟨n, ?_⟩
  rw [iteratedModuleJacobson_eq_ringJacobson_pow_smul_top, hn]
  simp

/-- A non-simple nonzero semisimple module contains two incomparable
submodules. -/
theorem exists_incomparable_submodules_of_semisimple_not_simple
    {E : Type v} [AddCommGroup E] [Module R E]
    [Nontrivial E] [IsSemisimpleModule R E]
    (hnot : ¬ IsSimpleModule R E) :
    ∃ P Q : Submodule R E, ¬ P ≤ Q ∧ ¬ Q ≤ P := by
  classical
  have hproper : ∃ P : Submodule R E, P ≠ ⊥ ∧ P ≠ ⊤ := by
    by_contra h
    push Not at h
    letI : IsSimpleOrder (Submodule R E) := {
      exists_pair_ne := exists_pair_ne (α := Submodule R E)
      eq_bot_or_eq_top := fun P ↦ by
        by_cases hP : P = ⊥
        · exact Or.inl hP
        · exact Or.inr (h P hP) }
    exact hnot IsSimpleModule.mk
  obtain ⟨P, hPbot, hPtop⟩ := hproper
  obtain ⟨Q, hPQ⟩ := exists_isCompl P
  have hQbot : Q ≠ ⊥ := by
    intro hQ
    apply hPtop
    simpa [hQ] using hPQ.sup_eq_top
  refine ⟨P, Q, ?_, ?_⟩
  · intro hle
    apply hPbot
    apply le_antisymm _ bot_le
    rw [← hPQ.inf_eq_bot]
    exact le_inf le_rfl hle
  · intro hle
    apply hQbot
    apply le_antisymm _ bot_le
    rw [← hPQ.inf_eq_bot]
    exact le_inf hle le_rfl

/-- If a finite radical filtration has simple nonzero tops at every stage,
then its initial module is uniserial. -/
theorem isUniserialModule_of_iteratedJacobson_tops_simple
    [IsNoetherian R M]
    (bound : ℕ)
    (hbot : iteratedModuleJacobson R M bound = ⊥)
    (hsimple : ∀ n < bound,
      iteratedModuleJacobson R M n ≠ ⊥ →
        IsSimpleModule R
          (iteratedModuleJacobson R M n ⧸
            Module.jacobson R (iteratedModuleJacobson R M n))) :
    IsUniserialModule R M := by
  have hstage : ∀ d i : ℕ, i + d = bound →
      IsUniserialModule R (iteratedModuleJacobson R M i) := by
    intro d
    induction d with
    | zero =>
        intro i hi
        have hiBound : i = bound := by simpa using hi
        have hiBot : iteratedModuleJacobson R M i = ⊥ := hiBound ▸ hbot
        letI : Subsingleton (iteratedModuleJacobson R M i) :=
          (iteratedModuleJacobson R M i).subsingleton_iff_eq_bot.mpr hiBot
        exact IsUniserialModule.of_subsingleton
    | succ d ih =>
        intro i hi
        by_cases hiBot : iteratedModuleJacobson R M i = ⊥
        · letI : Subsingleton (iteratedModuleJacobson R M i) :=
            (iteratedModuleJacobson R M i).subsingleton_iff_eq_bot.mpr hiBot
          exact IsUniserialModule.of_subsingleton
        · have hiLt : i < bound := by omega
          have hTop := hsimple i hiLt hiBot
          have hnext : IsUniserialModule R
              (iteratedModuleJacobson R M (i + 1)) := by
            apply ih (i + 1)
            omega
          have hRadical : IsUniserialModule R
              (Module.jacobson R (iteratedModuleJacobson R M i)) := by
            let e := (iteratedModuleJacobson R M i).equivSubtypeMap
              (Module.jacobson R (iteratedModuleJacobson R M i))
            apply IsUniserialModule.congr e.symm
            rw [iteratedModuleJacobson_succ] at hnext
            exact hnext
          exact IsUniserialModule.of_simpleTop_of_jacobson hTop hRadical
  have htop : IsUniserialModule R (iteratedModuleJacobson R M 0) := by
    apply hstage bound 0
    simp
  rw [iteratedModuleJacobson_zero] at htop
  exact IsUniserialModule.congr Submodule.topEquiv htop

/-- A nonuniserial noetherian module over a semiprimary ring has a radical
layer containing two incomparable submodules.  The returned submodules live
in the corresponding term of the radical filtration and contain its
intrinsic radical. -/
theorem exists_incomparable_over_jacobson_of_not_uniserial
    [IsSemiprimaryRing R] [IsNoetherian R M]
    (hM : ¬ IsUniserialModule R M) :
    ∃ n : ℕ, ∃ K L : Submodule R (iteratedModuleJacobson R M n),
      Module.jacobson R (iteratedModuleJacobson R M n) ≤ K ∧
      Module.jacobson R (iteratedModuleJacobson R M n) ≤ L ∧
      ¬ K ≤ L ∧ ¬ L ≤ K := by
  classical
  letI : IsArtinian R M :=
    IsSemiprimaryRing.isNoetherian_iff_isArtinian.mp inferInstance
  obtain ⟨bound, hbound⟩ :=
    iteratedModuleJacobson_eventually_eq_bot (R := R) (M := M)
  have hbad : ∃ n < bound,
      iteratedModuleJacobson R M n ≠ ⊥ ∧
        ¬ IsSimpleModule R
          (iteratedModuleJacobson R M n ⧸
            Module.jacobson R (iteratedModuleJacobson R M n)) := by
    by_contra h
    apply hM
    apply isUniserialModule_of_iteratedJacobson_tops_simple bound hbound
    intro n hn hne
    by_contra hnot
    exact h ⟨n, hn, hne, hnot⟩
  obtain ⟨n, hn, hstage, hnotSimple⟩ := hbad
  let E := iteratedModuleJacobson R M n
  let J : Submodule R E := Module.jacobson R E
  letI : Nontrivial E := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hstage (E.subsingleton_iff_eq_bot.mp hsub)
  letI : Nontrivial (E ⧸ J) :=
    Submodule.Quotient.nontrivial_iff.mpr (Module.jacobson_lt_top R E).ne
  letI : IsSemisimpleModule R (E ⧸ J) := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact Module.jacobson_quotient_jacobson R E
  obtain ⟨P, Q, hPQ, hQP⟩ :=
    exists_incomparable_submodules_of_semisimple_not_simple
      (R := R) hnotSimple
  let K : Submodule R E := P.comap J.mkQ
  let L : Submodule R E := Q.comap J.mkQ
  refine ⟨n, K, L, ?_, ?_, ?_, ?_⟩
  · exact J.le_comap_mkQ P
  · exact J.le_comap_mkQ Q
  · intro hKL
    apply hPQ
    exact (Submodule.comap_le_comap_iff_of_surjective J.mkQ_surjective).mp hKL
  · intro hLK
    apply hQP
    exact (Submodule.comap_le_comap_iff_of_surjective J.mkQ_surjective).mp hLK

/-- Ambient form of the preceding radical-layer witness. -/
theorem exists_incomparable_between_iteratedJacobson_of_not_uniserial
    [IsSemiprimaryRing R] [IsNoetherian R M]
    (hM : ¬ IsUniserialModule R M) :
    ∃ n : ℕ, ∃ K L : Submodule R M,
      iteratedModuleJacobson R M (n + 1) ≤ K ∧
      iteratedModuleJacobson R M (n + 1) ≤ L ∧
      K ≤ iteratedModuleJacobson R M n ∧
      L ≤ iteratedModuleJacobson R M n ∧
      ¬ K ≤ L ∧ ¬ L ≤ K := by
  obtain ⟨n, K, L, hJK, hJL, hKL, hLK⟩ :=
    exists_incomparable_over_jacobson_of_not_uniserial
      (R := R) (M := M) hM
  let E := iteratedModuleJacobson R M n
  let K' : Submodule R M := K.map E.subtype
  let L' : Submodule R M := L.map E.subtype
  refine ⟨n, K', L', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [iteratedModuleJacobson_succ]
    exact Submodule.map_mono hJK
  · rw [iteratedModuleJacobson_succ]
    exact Submodule.map_mono hJL
  · exact E.map_subtype_le K
  · exact E.map_subtype_le L
  · intro h
    apply hKL
    exact (Submodule.map_le_map_iff_of_injective E.subtype_injective K L).mp h
  · intro h
    apply hLK
    exact (Submodule.map_le_map_iff_of_injective E.subtype_injective L K).mp h

/-- For incomparable intermediate submodules in one radical layer, a quotient
map cannot differ from a map through the other quotient by a map whose image
lies in the target radical. -/
theorem quotientMap_sub_comp_range_not_le_jacobson
    [IsSemiprimaryRing R]
    {n : ℕ} {K L : Submodule R M}
    (hnextK : iteratedModuleJacobson R M (n + 1) ≤ K)
    (hLn : L ≤ iteratedModuleJacobson R M n)
    (hLK : ¬ L ≤ K)
    (t : (M ⧸ L) →ₗ[R] (M ⧸ K)) :
    ¬ LinearMap.range (K.mkQ - t.comp L.mkQ) ≤
      Module.jacobson R (M ⧸ K) := by
  obtain ⟨x, hxL, hxK⟩ := SetLike.not_le_iff_exists.mp hLK
  have hxLayer : x ∈ iteratedModuleJacobson R M n := hLn hxL
  have hLzero : L.mkQ x = 0 := by
    change (Submodule.Quotient.mk x : M ⧸ L) = 0
    exact (Submodule.Quotient.mk_eq_zero L).mpr hxL
  have hKne : K.mkQ x ≠ 0 := by
    change (Submodule.Quotient.mk x : M ⧸ K) ≠ 0
    intro hzero
    exact hxK ((Submodule.Quotient.mk_eq_zero K).mp hzero)
  have heval : (K.mkQ - t.comp L.mkQ) x = K.mkQ x := by
    simp [hLzero]
  have hnextTarget :
      iteratedModuleJacobson R (M ⧸ K) (n + 1) = ⊥ := by
    rw [← iteratedModuleJacobson_map_eq_of_surjective
      K.mkQ K.mkQ_surjective]
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzK : z ∈ K := hnextK hz
    simp only [Submodule.mem_bot]
    change (Submodule.Quotient.mk z : M ⧸ K) = 0
    exact (Submodule.Quotient.mk_eq_zero K).mpr hzK
  intro hrange
  have hxNext : (K.mkQ - t.comp L.mkQ) x ∈
      iteratedModuleJacobson R (M ⧸ K) (n + 1) :=
    iteratedModuleJacobson_apply_mem_succ_of_range_le_jacobson
      (K.mkQ - t.comp L.mkQ) hrange n hxLayer
  rw [hnextTarget, Submodule.mem_bot, heval] at hxNext
  exact hKne hxNext

end MagnitudeConjecture
