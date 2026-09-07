import MagnitudeConjecture.Algebra.BiserialModule
import MagnitudeConjecture.Algebra.SocleModule
import MagnitudeConjecture.CategoryTheory.BiserialObject

/-!
# Biserial modules from a two-summand radical decomposition

An explicit decomposition of the Jacobson radical into two uniserial
modules gives the two branches in the definition of a biserial module.  This
file records the elementary linear-algebra assembly separately from the
Auslander--Reiten argument which produces those branches.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture

/-- Intrinsic form of a radical decomposition into two uniserial branches
whose intersection is zero. -/
def HasSeparatedUniserialRadicalObject
    {C : Type*} [Category C] [Abelian C] (X : C) : Prop :=
  ∃ J U V : Subobject X,
    IsCoatom J ∧
      (∀ Q : Subobject X, IsCoatom Q → Q = J) ∧
      U ⊔ V = J ∧
      Std.Total ((· ≤ ·) : Set.Iic U → Set.Iic U → Prop) ∧
      Std.Total ((· ≤ ·) : Set.Iic V → Set.Iic V → Prop) ∧
      U ⊓ V = ⊥

namespace HasSeparatedUniserialRadicalObject

variable {C D : Type*} [Category C] [Abelian C]
variable [Category D] [Abelian D] {X : C} {Y : D}

/-- Separated radical branches are invariant under an order isomorphism of
subobject lattices. -/
theorem congrOrderIso
    (hX : HasSeparatedUniserialRadicalObject X)
    (e : Subobject X ≃o Subobject Y) :
    HasSeparatedUniserialRadicalObject Y := by
  obtain ⟨J, U, V, hJ, hJunique, hsup, hU, hV, hinf⟩ := hX
  refine ⟨e J, e U, e V, (e.isCoatom_iff J).2 hJ, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    have hQ' : IsCoatom (e.symm Q) := (e.symm.isCoatom_iff Q).2 hQ
    have : e.symm Q = J := hJunique _ hQ'
    simpa using congrArg e this
  · simpa only [map_sup] using congrArg e hsup
  · exact IsBiserialObject.total_of_orderIso (e.Iic U) hU
  · exact IsBiserialObject.total_of_orderIso (e.Iic V) hV
  · simpa only [map_inf, map_bot] using congrArg e hinf

/-- An equivalence sends separated radical branches to separated radical
branches. -/
theorem map_equivalence
    (hX : HasSeparatedUniserialRadicalObject X) (E : C ≌ D) :
    HasSeparatedUniserialRadicalObject (E.functor.obj X) :=
  congrOrderIso hX
    (MagnitudeConjecture.CategoryTheory.Equivalence.subobjectOrderIso E X)

/-- Separated radical branches of an equivalence image reflect to the
source. -/
theorem of_map_equivalence
    (E : C ≌ D)
    (hEX : HasSeparatedUniserialRadicalObject (E.functor.obj X)) :
    HasSeparatedUniserialRadicalObject X :=
  congrOrderIso hEX
    (MagnitudeConjecture.CategoryTheory.Equivalence.subobjectOrderIso E X).symm

end HasSeparatedUniserialRadicalObject

namespace IsBiserialModule

universe u v w₁ w₂

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {U : Type w₁} [AddCommGroup U] [Module R U]
variable {V : Type w₂} [AddCommGroup V] [Module R V]

/-- The preimage of a uniserial submodule along a surjection is uniserial
when the kernel is simple and essential in the source. -/
theorem IsUniserialModule.comap_of_simple_essential_kernel
    {N : Type w₁} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hker : IsSimpleModule R f.ker)
    (hessential : ∀ P : Submodule R M, P ≠ ⊥ → P ⊓ f.ker ≠ ⊥)
    (U : Submodule R N) (hU : IsUniserialModule R U) :
    IsUniserialModule R (U.comap f) := by
  let C : Submodule R M := U.comap f
  unfold IsUniserialModule
  constructor
  intro P Q
  by_cases hP : P = ⊥
  · exact Or.inl (hP ▸ bot_le)
  by_cases hQ : Q = ⊥
  · exact Or.inr (hQ ▸ bot_le)
  let P' : Submodule R M := P.map C.subtype
  let Q' : Submodule R M := Q.map C.subtype
  have hP'ne : P' ≠ ⊥ := by
    intro hzero
    apply hP
    apply Submodule.map_injective_of_injective C.subtype_injective
    simpa [P'] using hzero
  have hQ'ne : Q' ≠ ⊥ := by
    intro hzero
    apply hQ
    apply Submodule.map_injective_of_injective C.subtype_injective
    simpa [Q'] using hzero
  have hkerP : f.ker ≤ P' := by
    have hinter : P' ⊓ f.ker ≠ ⊥ := hessential P' hP'ne
    have heq : P' ⊓ f.ker = f.ker :=
      ((isSimpleModule_iff_isAtom.mp hker).le_iff_eq hinter).mp inf_le_right
    rw [← heq]
    exact inf_le_left
  have hkerQ : f.ker ≤ Q' := by
    have hinter : Q' ⊓ f.ker ≠ ⊥ := hessential Q' hQ'ne
    have heq : Q' ⊓ f.ker = f.ker :=
      ((isSimpleModule_iff_isAtom.mp hker).le_iff_eq hinter).mp inf_le_right
    rw [← heq]
    exact inf_le_left
  have hP'map : P'.map f ≤ U := by
    rintro y ⟨x, hx, rfl⟩
    have hxC : x ∈ C := (Submodule.map_subtype_le C P) hx
    exact hxC
  have hQ'map : Q'.map f ≤ U := by
    rintro y ⟨x, hx, rfl⟩
    have hxC : x ∈ C := (Submodule.map_subtype_le C Q) hx
    exact hxC
  let PU : Submodule R U := P'.map f |>.comap U.subtype
  let QU : Submodule R U := Q'.map f |>.comap U.subtype
  have hPUmap : PU.map U.subtype = P'.map f := by
    change (P'.map f |>.comap U.subtype).map U.subtype = P'.map f
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hP'map]
  have hQUmap : QU.map U.subtype = Q'.map f := by
    change (Q'.map f |>.comap U.subtype).map U.subtype = Q'.map f
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQ'map]
  rcases hU.total PU QU with hPQ | hQP
  · left
    apply (Submodule.map_le_map_iff_of_injective C.subtype_injective P Q).1
    change P' ≤ Q'
    rw [← Submodule.comap_map_eq_self hkerP,
      ← Submodule.comap_map_eq_self hkerQ]
    apply Submodule.comap_mono
    rw [← hPUmap, ← hQUmap]
    exact Submodule.map_mono hPQ
  · right
    apply (Submodule.map_le_map_iff_of_injective C.subtype_injective Q P).1
    change Q' ≤ P'
    rw [← Submodule.comap_map_eq_self hkerQ,
      ← Submodule.comap_map_eq_self hkerP]
    apply Submodule.comap_mono
    rw [← hQUmap, ← hPUmap]
    exact Submodule.map_mono hQP

/-- The Jacobson radical is the internal direct sum of two uniserial
submodules.  Zero branches are allowed. -/
def HasSeparatedUniserialJacobsonBranches
    (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ P Q : Submodule R M,
    P ⊔ Q = Module.jacobson R M ∧
      P ⊓ Q = ⊥ ∧
      IsUniserialModule R P ∧ IsUniserialModule R Q

/-- Separated uniserial radical branches are invariant under linear
equivalence. -/
theorem HasSeparatedUniserialJacobsonBranches.congr
    {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : HasSeparatedUniserialJacobsonBranches R M) :
    HasSeparatedUniserialJacobsonBranches R N := by
  obtain ⟨P, Q, hsup, hinf, hP, hQ⟩ := hM
  refine ⟨P.map e.toLinearMap, Q.map e.toLinearMap, ?_, ?_, ?_, ?_⟩
  · rw [← Submodule.map_sup, hsup]
    exact Module.map_jacobson_of_bijective e.bijective
  · rw [← Submodule.map_inf e.toLinearMap e.injective, hinf,
      Submodule.map_bot]
  · exact IsUniserialModule.congr (e.submoduleMap P) hP
  · exact IsUniserialModule.congr (e.submoduleMap Q) hQ

/-- Separated module-theoretic branches with simple top give the intrinsic
subobject-lattice form. -/
theorem HasSeparatedUniserialJacobsonBranches.toModuleCatObject
    (hM : HasSeparatedUniserialJacobsonBranches R M)
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    HasSeparatedUniserialRadicalObject (ModuleCat.of R M) := by
  obtain ⟨P, Q, hsup, hinf, hP, hQ⟩ := hM
  let e := ModuleCat.subobjectModule (ModuleCat.of R M)
  have hJ : IsCoatom (Module.jacobson R M) :=
    isSimpleModule_iff_isCoatom.mp htop
  refine ⟨e.symm (Module.jacobson R M), e.symm P, e.symm Q,
    (e.symm.isCoatom_iff _).2 hJ, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    apply e.injective
    simp only [OrderIso.apply_symm_apply]
    have hL' : IsCoatom (e L) := (e.isCoatom_iff L).2 hL
    apply (hJ.le_iff_eq hL'.ne_top).mp
    rw [Module.jacobson]
    exact sInf_le hL'
  · rw [← e.symm.map_sup, hsup]
  · exact IsBiserialObject.total_of_orderIso
      ((P.mapIic).trans (e.symm.Iic P)) hP
  · exact IsBiserialObject.total_of_orderIso
      ((Q.mapIic).trans (e.symm.Iic Q)) hQ
  · rw [← e.symm.map_inf, hinf, e.symm.map_bot]

/-- The intrinsic separated-branch condition on a module object recovers
separated module-theoretic Jacobson branches. -/
theorem hasSeparatedUniserialJacobsonBranches_of_moduleCatObject
    (hM : HasSeparatedUniserialRadicalObject (ModuleCat.of R M)) :
    HasSeparatedUniserialJacobsonBranches R M := by
  obtain ⟨J, P, Q, hJ, hJunique, hsup, hP, hQ, hinf⟩ := hM
  let e := ModuleCat.subobjectModule (ModuleCat.of R M)
  have hJmod : IsCoatom (e J) := (e.isCoatom_iff J).2 hJ
  have hJuniqueMod : ∀ L : Submodule R M, IsCoatom L → L = e J := by
    intro L hL
    have hL' : IsCoatom (e.symm L) := (e.symm.isCoatom_iff L).2 hL
    simpa using congrArg e (hJunique _ hL')
  have hjac : Module.jacobson R M = e J := by
    rw [Module.jacobson]
    apply le_antisymm
    · exact sInf_le hJmod
    · apply le_sInf
      intro L hL
      rw [hJuniqueMod L hL]
  refine ⟨e P, e Q, ?_, ?_, ?_, ?_⟩
  · rw [← e.map_sup, hsup, ← hjac]
  · rw [← e.map_inf, hinf, e.map_bot]
  · exact IsBiserialObject.total_of_orderIso
      ((e.Iic P).trans (e P).mapIic.symm) hP
  · exact IsBiserialObject.total_of_orderIso
      ((e.Iic Q).trans (e Q).mapIic.symm) hQ

/-- The separated module condition with simple top gives the intrinsic
condition in the finitely generated module category. -/
theorem HasSeparatedUniserialJacobsonBranches.toFGModuleCatObject
    [IsNoetherianRing R] (N : FGModuleCat R)
    (hN : HasSeparatedUniserialJacobsonBranches R N)
    (htop : IsSimpleModule R (N ⧸ Module.jacobson R N)) :
    HasSeparatedUniserialRadicalObject N := by
  letI : (ModuleCat.isFG R).IsClosedUnderSubobjects := {
    prop_of_mono := by
      intro X Y f _ hY
      letI : Module.Finite R Y := hY
      exact Module.Finite.of_injective f.hom
        ((ModuleCat.mono_iff_injective f).mp inferInstance) }
  letI : (ModuleCat.isFG R).ContainsZero := {
    exists_zero := ⟨ModuleCat.of R PUnit,
      ModuleCat.isZero_of_subsingleton _, by
      change Module.Finite R PUnit
      infer_instance⟩ }
  exact HasSeparatedUniserialRadicalObject.congrOrderIso
    (hN.toModuleCatObject htop)
    (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
      (ModuleCat.isFG R) N).symm

/-- The intrinsic separated condition in the finitely generated module
category recovers separated module-theoretic branches. -/
theorem hasSeparatedUniserialJacobsonBranches_of_fgModuleCatObject
    [IsNoetherianRing R] (N : FGModuleCat R)
    (hN : HasSeparatedUniserialRadicalObject N) :
    HasSeparatedUniserialJacobsonBranches R N := by
  letI : (ModuleCat.isFG R).IsClosedUnderSubobjects := {
    prop_of_mono := by
      intro X Y f _ hY
      letI : Module.Finite R Y := hY
      exact Module.Finite.of_injective f.hom
        ((ModuleCat.mono_iff_injective f).mp inferInstance) }
  letI : (ModuleCat.isFG R).ContainsZero := {
    exists_zero := ⟨ModuleCat.of R PUnit,
      ModuleCat.isZero_of_subsingleton _, by
      change Module.Finite R PUnit
      infer_instance⟩ }
  apply hasSeparatedUniserialJacobsonBranches_of_moduleCatObject
  exact HasSeparatedUniserialRadicalObject.congrOrderIso hN
    (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
      (ModuleCat.isFG R) N)

/-- A linear equivalence from the Jacobson radical to a product of two
uniserial modules supplies separated internal branches. -/
theorem hasSeparatedUniserialJacobsonBranches_of_linearEquiv_prod
    (e : (Module.jacobson R M) ≃ₗ[R] U × V)
    (hU : IsUniserialModule R U)
    (hV : IsUniserialModule R V) :
    HasSeparatedUniserialJacobsonBranches R M := by
  let J : Submodule R M := Module.jacobson R M
  let iU : U →ₗ[R] J :=
    e.symm.toLinearMap.comp (LinearMap.inl R U V)
  let iV : V →ₗ[R] J :=
    e.symm.toLinearMap.comp (LinearMap.inr R U V)
  let fU : U →ₗ[R] M := J.subtype.comp iU
  let fV : V →ₗ[R] M := J.subtype.comp iV
  let U' : Submodule R M := LinearMap.range fU
  let V' : Submodule R M := LinearMap.range fV
  have hiU : Function.Injective iU :=
    e.symm.injective.comp LinearMap.inl_injective
  have hiV : Function.Injective iV :=
    e.symm.injective.comp LinearMap.inr_injective
  have hfU : Function.Injective fU := J.subtype_injective.comp hiU
  have hfV : Function.Injective fV := J.subtype_injective.comp hiV
  have hU' : IsUniserialModule R U' :=
    IsUniserialModule.congr (LinearEquiv.ofInjective fU hfU) hU
  have hV' : IsUniserialModule R V' :=
    IsUniserialModule.congr (LinearEquiv.ofInjective fV hfV) hV
  have hsup : U' ⊔ V' = J := by
    apply le_antisymm
    · apply sup_le
      · rintro x ⟨u, rfl⟩
        exact (iU u).2
      · rintro x ⟨v, rfl⟩
        exact (iV v).2
    · intro x hx
      let z : J := ⟨x, hx⟩
      let u : U := (e z).1
      let v : V := (e z).2
      have hz : z = iU u + iV v := by
        apply e.injective
        simp [iU, iV, u, v]
      have hxsum : x = fU u + fV v := by
        exact congrArg Subtype.val hz
      rw [hxsum]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left ⟨u, rfl⟩)
        (Submodule.mem_sup_right ⟨v, rfl⟩)
  have hinf : U' ⊓ V' = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨u, hu⟩ := hx.1
      obtain ⟨v, hv⟩ := hx.2
      have huv : iU u = iV v := by
        apply J.subtype_injective
        exact hu.trans hv.symm
      have hpair : (u, 0) = (0, v) := by
        apply e.symm.injective
        simpa [iU, iV] using huv
      have hu0 : u = 0 := congrArg Prod.fst hpair
      rw [← hu, hu0, map_zero]
      exact Submodule.zero_mem _
    · exact bot_le
  exact ⟨U', V', hsup, hinf, hU', hV'⟩

/-- If the Jacobson radical is linearly equivalent to a product of two
uniserial modules, then the ambient module is biserial. -/
theorem of_jacobson_linearEquiv_prod
    (e : (Module.jacobson R M) ≃ₗ[R] U × V)
    (hU : IsUniserialModule R U)
    (hV : IsUniserialModule R V) :
    IsBiserialModule R M := by
  obtain ⟨P, Q, hsup, hinf, hP, hQ⟩ :=
    hasSeparatedUniserialJacobsonBranches_of_linearEquiv_prod e hU hV
  refine ⟨P, Q, hsup, hP, hQ, ?_⟩
  rw [hinf]
  exact IsSimpleOrZeroModule.of_subsingleton

/-- If the socle is simple and lies in the radical, separated uniserial
branches in the quotient by the socle lift to two uniserial branches whose
intersection is precisely that socle. -/
theorem of_quotient_moduleSocle_hasSeparatedUniserialJacobsonBranches
    [IsArtinian R M]
    (hsocle : IsSimpleModule R (moduleSocle R M))
    (hsocleRadical : moduleSocle R M ≤ Module.jacobson R M)
    (hquot : HasSeparatedUniserialJacobsonBranches
      R (M ⧸ moduleSocle R M)) :
    IsBiserialModule R M := by
  let S : Submodule R M := moduleSocle R M
  let q : M →ₗ[R] (M ⧸ S) := S.mkQ
  obtain ⟨Ubar, Vbar, hsupbar, hinfbar, hUbar, hVbar⟩ := hquot
  let U : Submodule R M := Ubar.comap q
  let V : Submodule R M := Vbar.comap q
  have hker : IsSimpleModule R q.ker := by
    rw [Submodule.ker_mkQ]
    exact hsocle
  have hessential : ∀ P : Submodule R M, P ≠ ⊥ → P ⊓ q.ker ≠ ⊥ := by
    intro P hP
    rw [Submodule.ker_mkQ]
    exact inf_moduleSocle_ne_bot P hP
  have hU : IsUniserialModule R U :=
    IsUniserialModule.comap_of_simple_essential_kernel
      q hker hessential Ubar hUbar
  have hV : IsUniserialModule R V :=
    IsUniserialModule.comap_of_simple_essential_kernel
      q hker hessential Vbar hVbar
  have hkerU : q.ker ≤ U := by
    intro x hx
    change q x ∈ Ubar
    rw [LinearMap.mem_ker.mp hx]
    exact Ubar.zero_mem
  have hkerV : q.ker ≤ V := by
    intro x hx
    change q x ∈ Vbar
    rw [LinearMap.mem_ker.mp hx]
    exact Vbar.zero_mem
  have hsup : U ⊔ V = Module.jacobson R M := by
    calc
      U ⊔ V = ((U ⊔ V).map q).comap q :=
        (Submodule.comap_map_eq_self
          (hkerU.trans le_sup_left)).symm
      _ = (Ubar ⊔ Vbar).comap q := by
        rw [Submodule.map_sup]
        congr 2
        · exact Submodule.map_comap_eq_self (by
            rw [LinearMap.range_eq_top.mpr S.mkQ_surjective]
            exact le_top)
        · exact Submodule.map_comap_eq_self (by
            rw [LinearMap.range_eq_top.mpr S.mkQ_surjective]
            exact le_top)
      _ = (Module.jacobson R (M ⧸ S)).comap q := by rw [hsupbar]
      _ = ((Module.jacobson R M).map q).comap q := by
        rw [Module.jacobson_quotient_of_le hsocleRadical]
      _ = Module.jacobson R M :=
        Submodule.comap_map_eq_self (by
          rw [Submodule.ker_mkQ]
          exact hsocleRadical)
  have hinf : U ⊓ V = S := by
    calc
      U ⊓ V = (Ubar ⊓ Vbar).comap q := by
        exact (Submodule.comap_inf Ubar Vbar q).symm
      _ = (⊥ : Submodule R (M ⧸ S)).comap q := by rw [hinfbar]
      _ = q.ker := rfl
      _ = S := Submodule.ker_mkQ S
  refine ⟨U, V, hsup, hU, hV, ?_⟩
  rw [hinf]
  exact IsSimpleOrZeroModule.of_simple hsocle

end IsBiserialModule
end MagnitudeConjecture
