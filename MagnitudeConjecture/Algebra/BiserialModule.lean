import MagnitudeConjecture.Algebra.UniserialModule
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Length

/-!
# Biserial modules

The radical of a biserial module is the sum of at most two uniserial
submodules whose intersection is simple or zero.  Zero summands are allowed,
so the definition also covers uniserial and semisimple local modules without
separate edge cases.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v

/-- A module is simple or zero.  The `Subsingleton` branch is the literal
zero-module alternative and does not require a chosen zero object. -/
def IsSimpleOrZeroModule
    (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Subsingleton M ∨ IsSimpleModule R M

namespace IsSimpleOrZeroModule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem of_subsingleton [Subsingleton M] : IsSimpleOrZeroModule R M :=
  Or.inl inferInstance

theorem of_simple (hM : IsSimpleModule R M) :
    IsSimpleOrZeroModule R M :=
  Or.inr hM

/-- Simplicity-or-zero is invariant under a linear equivalence. -/
theorem congr
    {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : IsSimpleOrZeroModule R M) :
    IsSimpleOrZeroModule R N := by
  rcases hM with hzero | hsimple
  · left
    exact e.toEquiv.subsingleton_congr.mp hzero
  · right
    letI : IsSimpleModule R M := hsimple
    exact IsSimpleModule.congr e.symm

end IsSimpleOrZeroModule

/-- The radical of `M` is a sum of at most two uniserial submodules with
simple or zero intersection. -/
def IsBiserialModule
    (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ U V : Submodule R M,
    U ⊔ V = Module.jacobson R M ∧
      IsUniserialModule R U ∧
      IsUniserialModule R V ∧
      IsSimpleOrZeroModule R (↥(U ⊓ V : Submodule R M))

namespace IsBiserialModule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Biseriality is invariant under a linear equivalence. -/
theorem congr
    {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : IsBiserialModule R M) :
    IsBiserialModule R N := by
  rcases hM with ⟨U, V, hsup, hU, hV, hinter⟩
  refine ⟨U.map e.toLinearMap, V.map e.toLinearMap, ?_, ?_, ?_, ?_⟩
  · rw [← Submodule.map_sup, hsup]
    exact Module.map_jacobson_of_bijective e.bijective
  · exact IsUniserialModule.congr (e.submoduleMap U) hU
  · exact IsUniserialModule.congr (e.submoduleMap V) hV
  · let eInf : (↥(U ⊓ V : Submodule R M)) ≃ₗ[R]
        ↥(U.map e.toLinearMap ⊓ V.map e.toLinearMap : Submodule R N) :=
      (e.submoduleMap (U ⊓ V)).trans
        (LinearEquiv.ofEq _ _
          (Submodule.map_inf e.toLinearMap e.injective))
    exact IsSimpleOrZeroModule.congr eInf hinter

/-- A module with uniserial radical is biserial, using the zero module as
the second branch. -/
theorem of_uniserial_jacobson
    (hJ : IsUniserialModule R (Module.jacobson R M)) :
    IsBiserialModule R M := by
  refine ⟨Module.jacobson R M, (⊥ : Submodule R M), by simp, hJ, ?_, ?_⟩
  · exact IsUniserialModule.of_subsingleton
  · rw [inf_bot_eq]
    exact IsSimpleOrZeroModule.of_subsingleton

/-- Every uniserial module is biserial. -/
theorem of_uniserial (hM : IsUniserialModule R M) :
    IsBiserialModule R M :=
  of_uniserial_jacobson (hM.submodule (Module.jacobson R M))

/-- A module with zero radical is biserial. -/
theorem of_jacobson_eq_bot
    (hJ : Module.jacobson R M = ⊥) :
    IsBiserialModule R M := by
  apply of_uniserial_jacobson
  rw [hJ]
  exact IsUniserialModule.of_subsingleton

/-- The canonical map from a submodule `P` to the quotient by another
submodule `Q`. -/
def submoduleToQuotientLinearMap
    (P Q : Submodule R M) : P →ₗ[R] (M ⧸ Q) :=
  Q.mkQ.comp P.subtype

/-- If two submodules meet trivially, the canonical map from either one to
the quotient by the other is injective. -/
theorem submoduleToQuotientLinearMap_injective_of_inf_eq_bot
    (P Q : Submodule R M) (hinf : P ⊓ Q = ⊥) :
    Function.Injective (submoduleToQuotientLinearMap P Q) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hxy' : Q.mkQ x.1 = Q.mkQ y.1 := hxy
  have hquot : Q.mkQ (x.1 - y.1) = 0 := by
    rw [map_sub, hxy', sub_self]
  have hQ : x.1 - y.1 ∈ Q := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hquot
    exact hquot
  have hPQ : x.1 - y.1 ∈ P ⊓ Q :=
    ⟨P.sub_mem x.2 y.2, hQ⟩
  rw [hinf] at hPQ
  exact hPQ

/-- A branch disjoint from `Q` is uniserial whenever the ambient quotient
by `Q` is uniserial. -/
theorem uniserial_submodule_of_uniserial_quotient_of_inf_eq_bot
    (P Q : Submodule R M) (hinf : P ⊓ Q = ⊥)
    (hquot : IsUniserialModule R (M ⧸ Q)) :
    IsUniserialModule R P :=
  IsUniserialModule.of_injective hquot
    (submoduleToQuotientLinearMap P Q)
    (submoduleToQuotientLinearMap_injective_of_inf_eq_bot P Q hinf)

/-- Zero-intersection branch of the local biserial induction.  If the
radical is the sum of two disjoint branches and both cross-quotients are
uniserial, then the module is biserial. -/
theorem of_jacobson_eq_sup_of_inf_eq_bot_of_quotients_uniserial
    (P Q : Submodule R M)
    (hsup : P ⊔ Q = Module.jacobson R M)
    (hinf : P ⊓ Q = ⊥)
    (hquotQ : IsUniserialModule R (M ⧸ Q))
    (hquotP : IsUniserialModule R (M ⧸ P)) :
    IsBiserialModule R M := by
  refine ⟨P, Q, hsup, ?_, ?_, ?_⟩
  · exact uniserial_submodule_of_uniserial_quotient_of_inf_eq_bot
      P Q hinf hquotQ
  · exact uniserial_submodule_of_uniserial_quotient_of_inf_eq_bot
      Q P (by simpa [inf_comm] using hinf) hquotP
  · rw [hinf]
    exact IsSimpleOrZeroModule.of_subsingleton

/-- If the radical is `P + Q`, quotienting by `Q` leaves precisely the image
of `P` as the radical. -/
theorem jacobson_quotient_eq_map_of_jacobson_eq_sup
    [IsArtinian R M]
    (P Q : Submodule R M)
    (hsup : P ⊔ Q = Module.jacobson R M) :
    Module.jacobson R (M ⧸ Q) = P.map Q.mkQ := by
  have hQJ : Q ≤ Module.jacobson R M := by
    rw [← hsup]
    exact le_sup_right
  rw [Module.jacobson_quotient_of_le hQJ, ← hsup,
    Submodule.map_sup, Q.mkQ_map_self, sup_bot_eq]

/-- A simple-top module whose radical is `P + Q` has a uniserial quotient
by `Q` when `P` is uniserial and the two branches are disjoint.  The image
of `P` is then the full radical of the quotient. -/
theorem uniserial_quotient_of_jacobson_eq_sup_of_inf_eq_bot
    [IsArtinian R M] [IsNoetherian R M]
    (P Q : Submodule R M)
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hsup : P ⊔ Q = Module.jacobson R M)
    (hinf : P ⊓ Q = ⊥)
    (hP : IsUniserialModule R P) :
    IsUniserialModule R (M ⧸ Q) := by
  have hQJ : Q ≤ Module.jacobson R M := by
    rw [← hsup]
    exact le_sup_right
  have hquotTop : IsSimpleModule R
      ((M ⧸ Q) ⧸ Module.jacobson R (M ⧸ Q)) := by
    rw [Module.jacobson_quotient_of_le hQJ]
    letI : IsSimpleModule R (M ⧸ Module.jacobson R M) := htop
    exact IsSimpleModule.congr
      (Submodule.quotientQuotientEquivQuotient Q
        (Module.jacobson R M) hQJ)
  let f : P →ₗ[R] (M ⧸ Q) := submoduleToQuotientLinearMap P Q
  have hf : Function.Injective f :=
    submoduleToQuotientLinearMap_injective_of_inf_eq_bot P Q hinf
  have hfrange : f.range = P.map Q.mkQ := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  let eP : P ≃ₗ[R] P.map Q.mkQ :=
    (LinearEquiv.ofInjective f hf).trans
      (LinearEquiv.ofEq _ _ hfrange)
  have hPmap : IsUniserialModule R (P.map Q.mkQ) :=
    IsUniserialModule.congr eP hP
  apply IsUniserialModule.of_simpleTop_of_jacobson hquotTop
  rw [jacobson_quotient_eq_map_of_jacobson_eq_sup P Q hsup]
  exact hPmap

/-- If a simple-top module is biserial and its radical again has simple
top, then it is uniserial.  Indeed, the two biserial branches cannot both be
proper in the radical, since every proper submodule of a simple-top module
lies in its Jacobson radical. -/
theorem uniserial_of_biserial_of_simple_top_of_jacobson
    [IsNoetherian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hbis : IsBiserialModule R M)
    (hJacTop : IsSimpleModule R
      ((Module.jacobson R M) ⧸
        Module.jacobson R (Module.jacobson R M))) :
    IsUniserialModule R M := by
  rcases hbis with ⟨U, V, hsup, hU, hV, -⟩
  let J : Submodule R M := Module.jacobson R M
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
  have hUmap : UJ.map J.subtype = U := by
    dsimp only [UJ]
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hUJ]
  have hVmap : VJ.map J.subtype = V := by
    dsimp only [VJ]
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hVJ]
  have hUVtop : UJ ⊔ VJ = ⊤ := by
    apply Submodule.map_injective_of_injective J.subtype_injective
    rw [Submodule.map_sup, hUmap, hVmap, hsup]
    simp [J]
  by_cases hUtop : UJ = ⊤
  · apply IsUniserialModule.of_simpleTop_of_jacobson htop
    have hUJlinear : IsUniserialModule R UJ := by
      let eU : UJ ≃ₗ[R] U := {
        toFun x := ⟨x.1.1, x.2⟩
        invFun x := ⟨⟨x.1, hUJ x.2⟩, x.2⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
      exact IsUniserialModule.congr eU.symm hU
    exact IsUniserialModule.congr
      (LinearEquiv.ofTop UJ hUtop) hUJlinear
  by_cases hVtop : VJ = ⊤
  · apply IsUniserialModule.of_simpleTop_of_jacobson htop
    have hVJlinear : IsUniserialModule R VJ := by
      let eV : VJ ≃ₗ[R] V := {
        toFun x := ⟨x.1.1, x.2⟩
        invFun x := ⟨⟨x.1, hVJ x.2⟩, x.2⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
      exact IsUniserialModule.congr eV.symm hV
    exact IsUniserialModule.congr
      (LinearEquiv.ofTop VJ hVtop) hVJlinear
  exfalso
  have hUrad : UJ ≤ Module.jacobson R J :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hJacTop hUtop
  have hVrad : VJ ≤ Module.jacobson R J :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hJacTop hVtop
  have htopLe : (⊤ : Submodule R J) ≤ Module.jacobson R J := by
    rw [← hUVtop]
    exact sup_le hUrad hVrad
  exact (isSimpleModule_iff_isCoatom.mp hJacTop).ne_top
    (top_unique htopLe)

/-- A simple module is uniserial. -/
theorem uniserial_of_simple (hM : IsSimpleModule R M) :
    IsUniserialModule R M := by
  letI : IsSimpleModule R M := hM
  unfold IsUniserialModule
  constructor
  intro U V
  rcases IsSimpleOrder.eq_bot_or_eq_top U with rfl | rfl
  · exact Or.inl bot_le
  · exact Or.inr le_top

/-- The image of a simple submodule under an injective linear map is simple.
-/
theorem simple_map_of_injective
    {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (P : Submodule R M) (hP : IsSimpleModule R P) :
    IsSimpleModule R (P.map f) := by
  let g := f.domRestrict P
  let e : P ≃ₗ[R] LinearMap.range g :=
    LinearEquiv.ofInjective g (hf.comp P.subtype_injective)
  have hrange : LinearMap.range g = P.map f := by
    ext y
    simp [g]
  rw [← hrange]
  letI : IsSimpleModule R P := hP
  exact IsSimpleModule.congr e.symm

/-- A finite-length module of composition length one is uniserial. -/
theorem uniserial_of_length_eq_one
    (hM : Module.length R M = 1) :
    IsUniserialModule R M :=
  uniserial_of_simple (Module.length_eq_one_iff.mp hM)

/-- A finite-length module with simple top and composition length two is
uniserial. -/
theorem uniserial_of_simple_top_of_length_eq_two
    [IsNoetherian R M] [IsArtinian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hlength : Module.length R M = 2) :
    IsUniserialModule R M := by
  let J : Submodule R M := Module.jacobson R M
  have htopLength : Module.length R (M ⧸ J) = 1 :=
    Module.length_eq_one_iff.mpr htop
  have hlengthExact :
      Module.length R M = Module.length R J + Module.length R (M ⧸ J) :=
    Module.length_eq_add_of_exact
      J.subtype J.mkQ J.subtype_injective J.mkQ_surjective
      (LinearMap.exact_subtype_mkQ J)
  have hJLength : Module.length R J = 1 := by
    rw [hlength, htopLength] at hlengthExact
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R J + 1 = 2 := hlengthExact.symm
      _ = 1 + 1 := by norm_num
  exact IsUniserialModule.of_simpleTop_of_jacobson
    htop (uniserial_of_length_eq_one hJLength)

/-- Two incomparable submodules of a finite-length module of composition
length two are complementary simple submodules. -/
theorem simple_isCompl_of_length_eq_two_of_incomparable
    [IsNoetherian R M] [IsArtinian R M]
    (hlength : Module.length R M = 2)
    {P Q : Submodule R M} (hPQ : ¬ P ≤ Q) (hQP : ¬ Q ≤ P) :
    IsSimpleModule R P ∧ IsSimpleModule R Q ∧ IsCompl P Q := by
  have hPbot : P ≠ ⊥ := fun h ↦ hPQ (h.le.trans bot_le)
  have hQbot : Q ≠ ⊥ := fun h ↦ hQP (h.le.trans bot_le)
  have hPtop : P ≠ ⊤ := by
    intro h
    apply hQP
    simp [h]
  have hQtop : Q ≠ ⊤ := by
    intro h
    apply hPQ
    simp [h]
  have hPlengthPos : 0 < Module.length R P :=
    Module.length_pos_iff.mpr (by
      rw [Submodule.nontrivial_iff_ne_bot]
      exact hPbot)
  have hQlengthPos : 0 < Module.length R Q :=
    Module.length_pos_iff.mpr (by
      rw [Submodule.nontrivial_iff_ne_bot]
      exact hQbot)
  have hPlengthLt : Module.length R P < 2 := by
    simpa [hlength] using Submodule.length_lt (R := R) hPtop
  have hQlengthLt : Module.length R Q < 2 := by
    simpa [hlength] using Submodule.length_lt (R := R) hQtop
  have hPlength : Module.length R P = 1 := by
    apply le_antisymm
    · exact ENat.lt_two_iff.mp hPlengthLt
    · exact Order.one_le_iff_ne_zero.mpr hPlengthPos.ne'
  have hQlength : Module.length R Q = 1 := by
    apply le_antisymm
    · exact ENat.lt_two_iff.mp hQlengthLt
    · exact Order.one_le_iff_ne_zero.mpr hQlengthPos.ne'
  have hPsimple : IsSimpleModule R P :=
    Module.length_eq_one_iff.mp hPlength
  have hQsimple : IsSimpleModule R Q :=
    Module.length_eq_one_iff.mp hQlength
  have hPatom : IsAtom P := isSimpleModule_iff_isAtom.mp hPsimple
  have hinf : P ⊓ Q = ⊥ := by
    rcases hPatom.le_iff.mp inf_le_left with hbot | heq
    · exact hbot
    · exfalso
      apply hPQ
      rw [← heq]
      exact inf_le_right
  have hPquotLength : Module.length R (M ⧸ P) = 1 := by
    have hexact : Module.length R M =
        Module.length R P + Module.length R (M ⧸ P) :=
      Module.length_eq_add_of_exact
        P.subtype P.mkQ P.subtype_injective P.mkQ_surjective
        (LinearMap.exact_subtype_mkQ P)
    rw [hlength, hPlength] at hexact
    apply WithTop.add_left_cancel ENat.one_ne_top
    calc
      1 + Module.length R (M ⧸ P) = 2 := hexact.symm
      _ = 1 + 1 := by norm_num
  have hPcoatom : IsCoatom P :=
    isSimpleModule_iff_isCoatom.mp
      (Module.length_eq_one_iff.mp hPquotLength)
  have hPltSup : P < P ⊔ Q := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hsup
    apply hQP
    exact le_sup_right.trans hsup.symm.le
  have hsup : P ⊔ Q = ⊤ := hPcoatom.2 _ hPltSup
  exact ⟨hPsimple, hQsimple,
    ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩⟩

/-- An indecomposable finite-length module of composition length two is
uniserial. -/
theorem uniserial_of_indec_of_length_eq_two
    [IsNoetherian R M] [IsArtinian R M]
    (hindec :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M)
    (hlength : Module.length R M = 2) :
    IsUniserialModule R M := by
  unfold IsUniserialModule
  constructor
  intro P Q
  by_cases hPQ : P ≤ Q
  · exact Or.inl hPQ
  by_cases hQP : Q ≤ P
  · exact Or.inr hQP
  have hcompl : IsCompl P Q :=
    (simple_isCompl_of_length_eq_two_of_incomparable
      hlength hPQ hQP).2.2
  rcases hindec.eq_bot_or_eq_bot hcompl with hPbot | hQbot
  · exact Or.inl (hPbot.le.trans bot_le)
  · exact Or.inr (hQbot.le.trans bot_le)

/-- A composition-length-three module with simple top has radical of
composition length two. -/
theorem jacobson_length_eq_two_of_simple_top_of_length_eq_three
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hlength : Module.length R M = 3) :
    Module.length R (Module.jacobson R M) = 2 := by
  let J : Submodule R M := Module.jacobson R M
  have htopLength : Module.length R (M ⧸ J) = 1 :=
    Module.length_eq_one_iff.mpr htop
  have hlengthExact :
      Module.length R M = Module.length R J + Module.length R (M ⧸ J) :=
    Module.length_eq_add_of_exact
      J.subtype J.mkQ J.subtype_injective J.mkQ_surjective
      (LinearMap.exact_subtype_mkQ J)
  rw [hlength, htopLength] at hlengthExact
  apply WithTop.add_right_cancel ENat.one_ne_top
  calc
    Module.length R J + 1 = 3 := hlengthExact.symm
    _ = 2 + 1 := by norm_num

/-- A composition-length-three module with simple top and indecomposable
radical is uniserial. -/
theorem uniserial_of_simple_top_of_length_eq_three_of_jacobson_indec
    [IsNoetherian R M] [IsArtinian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hlength : Module.length R M = 3)
    (hradIndec :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R
        (Module.jacobson R M)) :
    IsUniserialModule R M := by
  apply IsUniserialModule.of_simpleTop_of_jacobson htop
  exact uniserial_of_indec_of_length_eq_two hradIndec
    (jacobson_length_eq_two_of_simple_top_of_length_eq_three htop hlength)

/-- A finite-length module of composition length three with simple top is
biserial.  If its radical is not already uniserial, its two incomparable
submodules are complementary simples. -/
theorem of_simple_top_of_length_eq_three
    [IsNoetherian R M] [IsArtinian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hlength : Module.length R M = 3) :
    IsBiserialModule R M := by
  let J : Submodule R M := Module.jacobson R M
  have hJLength : Module.length R J = 2 :=
    jacobson_length_eq_two_of_simple_top_of_length_eq_three htop hlength
  by_cases hJuniserial : IsUniserialModule R J
  · exact of_uniserial_jacobson hJuniserial
  · rw [IsUniserialModule, total_def] at hJuniserial
    push Not at hJuniserial
    obtain ⟨P, Q, hPQ, hQP⟩ := hJuniserial
    obtain ⟨hPsimple, hQsimple, hPQcompl⟩ :=
      simple_isCompl_of_length_eq_two_of_incomparable
        hJLength hPQ hQP
    let U : Submodule R M := P.map J.subtype
    let V : Submodule R M := Q.map J.subtype
    have hUsimple : IsSimpleModule R U :=
      simple_map_of_injective J.subtype J.subtype_injective P hPsimple
    have hVsimple : IsSimpleModule R V :=
      simple_map_of_injective J.subtype J.subtype_injective Q hQsimple
    have hsup : U ⊔ V = Module.jacobson R M := by
      change P.map J.subtype ⊔ Q.map J.subtype = J
      rw [← Submodule.map_sup, hPQcompl.sup_eq_top]
      simp
    have hinf : U ⊓ V = ⊥ := by
      change P.map J.subtype ⊓ Q.map J.subtype = ⊥
      rw [← Submodule.map_inf J.subtype J.subtype_injective,
        hPQcompl.inf_eq_bot]
      simp
    refine ⟨U, V, hsup, uniserial_of_simple hUsimple,
      uniserial_of_simple hVsimple, ?_⟩
    rw [hinf]
    exact IsSimpleOrZeroModule.of_subsingleton

end IsBiserialModule

end MagnitudeConjecture
