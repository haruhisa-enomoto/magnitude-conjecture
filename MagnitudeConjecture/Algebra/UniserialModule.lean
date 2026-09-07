import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.Algebra.Ring.GeomSum
import QuotientSubmoduleEquidistribution.Foundation.RingTheory.KrullSchmidt.Indecomposable

/-!
# Uniserial modules

This file supplies the small generic module-lattice layer needed by the
multiplicity-one part of the magnitude argument.  The definition and proofs
are adapted from the uniserial-module reductions in
`quotient-submodule-equidistribution` at commit
`20ee4b964a9174b15304ac96485beeb73be113d8`; no theorem specific to that
project is imported.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v w

/-- If a scalar is nilpotent on one vector, then `1 + u` is invertible on
that vector by a finite geometric sum. -/
theorem exists_smul_one_add_eq_of_pow_smul_eq_zero
    {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (u : R) (b : M) (n : ℕ) (hn : u ^ n • b = 0) :
    ∃ e : R, e • ((1 + u) • b) = b := by
  let e : R := ∑ i ∈ Finset.range n, (-u) ^ i
  refine ⟨e, ?_⟩
  calc
    e • ((1 + u) • b) = (e * (1 + u)) • b :=
      (mul_smul e (1 + u) b).symm
    _ = (1 - (-u) ^ n) • b := by
      rw [show (1 + u : R) = 1 - (-u) by simp, geom_sum_mul_neg]
    _ = b := by
      rw [sub_smul, one_smul]
      suffices (-u) ^ n • b = 0 by rw [this, sub_zero]
      rw [neg_pow, mul_smul, hn, smul_zero]

/-- The basis expansion of a vector, split into one nonzero coordinate and
the remaining support. -/
theorem basis_sum_repr_support_erase
    {k : Type u} [Field k]
    {I : Type v} [DecidableEq I]
    {V : Type w} [AddCommGroup V] [Module k V]
    (b : Module.Basis I k V) (g : V) (p : I)
    (hp : p ∈ (b.repr g).support) :
    g = b.repr g p • b p +
      ∑ q ∈ (b.repr g).support.erase p, b.repr g q • b q := by
  have hrepr : (b.repr g).sum (fun q d ↦ d • b q) = g := by
    change Finsupp.linearCombination k (fun q ↦ b q) (b.repr g) = g
    rw [← b.repr_symm_apply]
    exact b.repr.symm_apply_apply g
  calc
    g = (b.repr g).sum (fun q d ↦ d • b q) := hrepr.symm
    _ = b.repr g p • b p +
        ∑ q ∈ (b.repr g).support.erase p, b.repr g q • b q := by
      change (∑ q ∈ (b.repr g).support, b.repr g q • b q) = _
      rw [← Finset.sum_erase_add _ _ hp, add_comm]

/-- A module is uniserial when any two of its submodules are comparable. -/
def IsUniserialModule
    (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Std.Total ((· ≤ ·) : Submodule R M → Submodule R M → Prop)

/-- A linear equivalence induces an equivalence between module tops. -/
def moduleTopLinearEquiv
    {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M ≃ₗ[R] N) :
    (M ⧸ Module.jacobson R M) ≃ₗ[R]
      (N ⧸ Module.jacobson R N) :=
  Submodule.Quotient.equiv (Module.jacobson R M) (Module.jacobson R N) f
    (Module.map_jacobson_of_bijective f.bijective)

/-- Simplicity of the module top is invariant under a linear equivalence. -/
theorem isSimpleModule_top_congr
    {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M ≃ₗ[R] N)
    (hM : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    IsSimpleModule R (N ⧸ Module.jacobson R N) := by
  letI : IsSimpleModule R (M ⧸ Module.jacobson R M) := hM
  exact IsSimpleModule.congr (moduleTopLinearEquiv f).symm

/-- Quotienting by a submodule of the radical preserves a simple top. -/
theorem isSimpleModule_top_quotient_of_le_jacobson
    {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K ≤ Module.jacobson R M)
    (hM : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    IsSimpleModule R
      ((M ⧸ K) ⧸ Module.jacobson R (M ⧸ K)) := by
  rw [Module.jacobson_quotient_of_le hK]
  letI : IsSimpleModule R (M ⧸ Module.jacobson R M) := hM
  exact IsSimpleModule.congr
    (Submodule.quotientQuotientEquivQuotient K
      (Module.jacobson R M) hK)

namespace IsUniserialModule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Quotients of uniserial modules are uniserial. -/
theorem quotient (hM : IsUniserialModule R M)
    (P : Submodule R M) :
    IsUniserialModule R (M ⧸ P) := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro Q T
  rcases hM.total (Q.comap P.mkQ) (T.comap P.mkQ) with hQT | hTQ
  · exact Or.inl
      ((Submodule.comap_le_comap_iff_of_surjective
        P.mkQ_surjective).mp hQT)
  · exact Or.inr
      ((Submodule.comap_le_comap_iff_of_surjective
        P.mkQ_surjective).mp hTQ)

/-- Submodules of uniserial modules are uniserial. -/
theorem submodule (hM : IsUniserialModule R M)
    (P : Submodule R M) :
    IsUniserialModule R P := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro Q T
  rcases hM.total (Q.map P.subtype) (T.map P.subtype) with hQT | hTQ
  · exact Or.inl
      ((Submodule.map_le_map_iff_of_injective
        P.subtype_injective Q T).mp hQT)
  · exact Or.inr
      ((Submodule.map_le_map_iff_of_injective
        P.subtype_injective T Q).mp hTQ)

/-- In a uniserial module, either of two elements is a scalar multiple of
the other.  This is cyclic-submodule comparability in element form. -/
theorem smul_comparable (hM : IsUniserialModule R M) (x y : M) :
    (∃ r : R, r • x = y) ∨ (∃ r : R, r • y = x) := by
  unfold IsUniserialModule at hM
  rcases hM.total (Submodule.span R {x}) (Submodule.span R {y}) with hxy | hyx
  · right
    exact Submodule.mem_span_singleton.mp
      (hxy (Submodule.mem_span_singleton_self x))
  · left
    exact Submodule.mem_span_singleton.mp
      (hyx (Submodule.mem_span_singleton_self y))

/-- Elementwise comparability of cyclic submodules implies uniseriality. -/
theorem of_smul_comparable
    (h : ∀ x y : M,
      (∃ r : R, r • x = y) ∨ (∃ r : R, r • y = x)) :
    IsUniserialModule R M := by
  unfold IsUniserialModule
  constructor
  intro P Q
  by_cases hPQ : P ≤ Q
  · exact Or.inl hPQ
  · right
    obtain ⟨p, hpP, hpQ⟩ := SetLike.not_le_iff_exists.mp hPQ
    intro q hqQ
    rcases h p q with hpq | hqp
    · obtain ⟨r, hr⟩ := hpq
      rw [← hr]
      exact P.smul_mem r hpP
    · obtain ⟨r, hr⟩ := hqp
      exfalso
      exact hpQ (hr ▸ Q.smul_mem r hqQ)

/-- A surjective linear image of a uniserial module is uniserial. -/
theorem of_surjective
    (hM : IsUniserialModule R M)
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    IsUniserialModule R N := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro P Q
  rcases hM.total (P.comap f) (Q.comap f) with hPQ | hQP
  · exact Or.inl
      ((Submodule.comap_le_comap_iff_of_surjective hf).mp hPQ)
  · exact Or.inr
      ((Submodule.comap_le_comap_iff_of_surjective hf).mp hQP)

/-- A module which embeds in a uniserial module is uniserial. -/
theorem of_injective
    (hM : IsUniserialModule R M)
    (f : N →ₗ[R] M) (hf : Function.Injective f) :
    IsUniserialModule R N := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro P Q
  rcases hM.total (P.map f) (Q.map f) with hPQ | hQP
  · exact Or.inl
      ((Submodule.map_le_map_iff_of_injective hf P Q).mp hPQ)
  · exact Or.inr
      ((Submodule.map_le_map_iff_of_injective hf Q P).mp hQP)

/-- Uniseriality is invariant under a linear equivalence. -/
theorem congr
    (e : M ≃ₗ[R] N)
    (hM : IsUniserialModule R M) :
    IsUniserialModule R N := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro P Q
  rcases hM.total
      (Submodule.comap e.toLinearMap P)
      (Submodule.comap e.toLinearMap Q) with hPQ | hQP
  · exact Or.inl
      ((Submodule.comap_le_comap_iff_of_surjective e.surjective).mp hPQ)
  · exact Or.inr
      ((Submodule.comap_le_comap_iff_of_surjective e.surjective).mp hQP)

/-- Every subsingleton module is uniserial. -/
theorem of_subsingleton [Subsingleton M] :
    IsUniserialModule R M := by
  unfold IsUniserialModule
  constructor
  intro P Q
  left
  exact Subsingleton.elim P Q ▸ le_rfl

/-- A nonzero uniserial module is indecomposable. -/
theorem isIndecomposableModule
    (hM : IsUniserialModule R M) [Nontrivial M] :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  unfold IsUniserialModule at hM
  apply
    QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
  intro P Q hcompl
  rcases hM.total P Q with hPQ | hQP
  · left
    apply le_antisymm
    · calc
        P ≤ P ⊓ Q := le_inf le_rfl hPQ
        _ = ⊥ := hcompl.inf_eq_bot
    · exact bot_le
  · right
    apply le_antisymm
    · calc
        Q ≤ P ⊓ Q := le_inf hQP le_rfl
        _ = ⊥ := hcompl.inf_eq_bot
    · exact bot_le

/-- A nonzero indecomposable semisimple module is simple. -/
theorem isSimpleModule_of_semisimple_of_isIndecomposableModule
    (hM :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M)
    [IsSemisimpleModule R M] :
    IsSimpleModule R M := by
  letI : Nontrivial M := hM.nontrivial
  letI : IsSimpleOrder (Submodule R M) := {
    exists_pair_ne := exists_pair_ne (α := Submodule R M)
    eq_bot_or_eq_top := fun P ↦ by
      obtain ⟨Q, hPQ⟩ := exists_isCompl P
      rcases hM.eq_bot_or_eq_bot hPQ with hP | hQ
      · exact Or.inl hP
      · exact Or.inr (by
          have hsup := hPQ.sup_eq_top
          simpa [hQ] using hsup) }
  exact IsSimpleModule.mk

/-- The top of a nonzero finite-length uniserial module is simple. -/
theorem top_isSimple
    [Nontrivial M] [IsArtinian R M] [IsNoetherian R M]
    (hM : IsUniserialModule R M) :
    IsSimpleModule R (M ⧸ Module.jacobson R M) := by
  have hradicalNeTop : Module.jacobson R M ≠ ⊤ :=
    (Module.jacobson_lt_top R M).ne
  letI : Nontrivial (M ⧸ Module.jacobson R M) :=
    Submodule.Quotient.nontrivial_iff.mpr hradicalNeTop
  have htopUniserial :
      IsUniserialModule R (M ⧸ Module.jacobson R M) :=
    hM.quotient (Module.jacobson R M)
  have htopIndecomposable :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R
        (M ⧸ Module.jacobson R M) :=
    htopUniserial.isIndecomposableModule
  letI : IsSemisimpleModule R (M ⧸ Module.jacobson R M) := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact Module.jacobson_quotient_jacobson R M
  exact
    isSimpleModule_of_semisimple_of_isIndecomposableModule
      htopIndecomposable

/-- In a finite-length uniserial module, submodules of equal composition
length coincide. -/
theorem eq_of_length_eq
    [IsArtinian R M] [IsNoetherian R M]
    (hM : IsUniserialModule R M)
    {P Q : Submodule R M}
    (hlength : Module.length R P = Module.length R Q) :
    P = Q := by
  unfold IsUniserialModule at hM
  rcases hM.total P Q with hPQ | hQP
  · by_contra hne
    have hlt : P < Q := lt_of_le_of_ne hPQ hne
    have hlengthLt : Module.length R P < Module.length R Q := by
      simpa only [Module.length_submodule] using
        (Submodule.height_strictMono hlt)
    exact (ne_of_lt hlengthLt) hlength
  · by_contra hne
    have hlt : Q < P := lt_of_le_of_ne hQP (Ne.symm hne)
    have hlengthLt : Module.length R Q < Module.length R P := by
      simpa only [Module.length_submodule] using
        (Submodule.height_strictMono hlt)
    exact (ne_of_lt hlengthLt) hlength.symm

/-- If the top of a noetherian module is simple, every proper submodule lies
in its Jacobson radical. -/
theorem le_jacobson_of_ne_top_of_simple_top
    [IsNoetherian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    {P : Submodule R M} (hP : P ≠ ⊤) :
    P ≤ Module.jacobson R M := by
  let J : Submodule R M := Module.jacobson R M
  have hJcoatom : IsCoatom J :=
    isSimpleModule_iff_isCoatom.mp htop
  obtain ⟨Q, hQcoatom, hPQ⟩ :=
    (eq_top_or_exists_le_coatom P).resolve_left hP
  have hJQ : J ≤ Q := sInf_le hQcoatom
  have hJQeq : J = Q := by
    by_cases hEq : J = Q
    · exact hEq
    have hlt : J < Q := lt_of_le_of_ne hJQ hEq
    exact (hQcoatom.ne_top (hJcoatom.2 _ hlt)).elim
  change P ≤ J
  rw [hJQeq]
  exact hPQ

/-- A noetherian module with simple top is indecomposable. -/
theorem isIndecomposableModule_of_simpleTop
    [IsNoetherian R M]
    (hTop : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  let J : Submodule R M := Module.jacobson R M
  have hJcoatom : IsCoatom J :=
    isSimpleModule_iff_isCoatom.mp hTop
  have hMnontrivial : Nontrivial M := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have hJtop : J = ⊤ := by
      apply top_unique
      intro x _
      exact Subsingleton.elim x 0 ▸ J.zero_mem
    exact hJcoatom.ne_top hJtop
  letI : Nontrivial M := hMnontrivial
  apply
    QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
  intro P Q hPQ
  by_cases hPtop : P = ⊤
  · right
    have hinf := hPQ.inf_eq_bot
    simpa [hPtop] using hinf
  by_cases hQtop : Q = ⊤
  · left
    have hinf := hPQ.inf_eq_bot
    simpa [hQtop] using hinf
  exfalso
  have hPJ : P ≤ J :=
    le_jacobson_of_ne_top_of_simple_top hTop hPtop
  have hQJ : Q ≤ J :=
    le_jacobson_of_ne_top_of_simple_top hTop hQtop
  have htopLe : (⊤ : Submodule R M) ≤ J := by
    rw [← hPQ.sup_eq_top]
    exact sup_le hPJ hQJ
  exact hJcoatom.ne_top (top_unique htopLe)

/-- A noetherian module with simple top and uniserial radical is uniserial. -/
theorem of_simpleTop_of_jacobson
    [IsNoetherian R M]
    (hTop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hRadical : IsUniserialModule R (Module.jacobson R M)) :
    IsUniserialModule R M := by
  let J : Submodule R M := Module.jacobson R M
  unfold IsUniserialModule at hRadical ⊢
  constructor
  intro P Q
  by_cases hPTop : P = ⊤
  · right
    simp [hPTop]
  by_cases hQTop : Q = ⊤
  · left
    simp [hQTop]
  have hPJ : P ≤ J :=
    le_jacobson_of_ne_top_of_simple_top hTop hPTop
  have hQJ : Q ≤ J :=
    le_jacobson_of_ne_top_of_simple_top hTop hQTop
  let P' : Submodule R J := Submodule.comap J.subtype P
  let Q' : Submodule R J := Submodule.comap J.subtype Q
  have hPMap : Submodule.map J.subtype P' = P := by
    dsimp only [P']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPJ]
  have hQMap : Submodule.map J.subtype Q' = Q := by
    dsimp only [Q']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQJ]
  rcases hRadical.total P' Q' with hPQ | hQP
  · left
    rw [← hPMap, ← hQMap]
    exact Submodule.map_mono hPQ
  · right
    rw [← hPMap, ← hQMap]
    exact Submodule.map_mono hQP

/-- A proper submodule of a finite-length uniserial submodule has an
immediate successor whose intrinsic radical is exactly the original
submodule.  This is the one-step extension used in the biserial induction.
-/
theorem exists_covBy_le_with_comap_eq_jacobson
    [IsArtinian R M] [IsNoetherian R M]
    (U : Submodule R M) (hU : IsUniserialModule R U)
    {E : Submodule R M} (hE : E < U) :
    ∃ C : Submodule R M,
      E ⋖ C ∧ C ≤ U ∧ IsUniserialModule R C ∧
        E.comap C.subtype = Module.jacobson R C := by
  obtain ⟨C, hEC, hCU⟩ := exists_covBy_le_of_lt hE
  let fCU : C →ₗ[R] U :=
    C.subtype.codRestrict U (fun x ↦ hCU x.2)
  have hfCU : Function.Injective fCU := by
    intro x y hxy
    have hval : (x.1 : M) = y.1 :=
      congrArg (fun z : U ↦ (z : M)) hxy
    exact Subtype.ext hval
  have hCuni : IsUniserialModule R C :=
    IsUniserialModule.of_injective hU fCU hfCU
  refine ⟨C, hEC, hCU, hCuni, ?_⟩
  let EC : Submodule R C := E.comap C.subtype
  have hECtop : EC ≠ ⊤ := by
    intro htop
    have hCleE : C ≤ E := by
      intro x hx
      have hxEC : (⟨x, hx⟩ : C) ∈ EC :=
        htop.symm ▸ Submodule.mem_top
      exact hxEC
    exact hEC.1.2 hCleE
  have hCneBot : C ≠ ⊥ := by
    intro hCbot
    have hEleBot : E ≤ ⊥ := by
      simpa [hCbot] using hEC.le
    have hEbot : E = ⊥ := le_antisymm hEleBot bot_le
    exact hEC.ne (hEbot.trans hCbot.symm)
  letI : Nontrivial C := Submodule.nontrivial_iff_ne_bot.mpr hCneBot
  have hCtop : IsSimpleModule R (C ⧸ Module.jacobson R C) :=
    hCuni.top_isSimple
  have hECle : EC ≤ Module.jacobson R C :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hCtop hECtop
  have hECcoatom : IsCoatom EC := by
    rw [← isSimpleModule_iff_isCoatom]
    exact (covBy_iff_quot_is_simple hEC.le).mp hEC
  apply le_antisymm
  · exact hECle
  · by_contra hnot
    have hne : EC ≠ Module.jacobson R C := by
      intro heq
      exact hnot heq.ge
    have hlt : EC < Module.jacobson R C :=
      lt_of_le_of_ne hECle hne
    have htop : Module.jacobson R C = ⊤ := hECcoatom.2 _ hlt
    exact (Module.jacobson_lt_top R C).ne htop

end IsUniserialModule

end MagnitudeConjecture
