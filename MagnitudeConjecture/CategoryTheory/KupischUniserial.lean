import MagnitudeConjecture.Algebra.LocalRingJacobson
import MagnitudeConjecture.Algebra.UniserialModule
import MagnitudeConjecture.CategoryTheory.KupischCyclicity
import MagnitudeConjecture.LinearAlgebra.LocalAlgebraResidue
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Kupisch's one-sided uniserial alternative

This file upgrades distributive Hom-bimodule chains to the exact condition
used by Skowroński--Waschbüsch.  Finite-dimensionality first supplies a
largest principal two-sided span.  Kupisch cyclicity orients that generator
to one endpoint.  On endomorphism rings the same construction gives a
generator of the Jacobson radical; nilpotence and the algebraically closed
residue character make the endpoint regular modules uniserial.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Transit collapses a principal two-sided span to target-endomorphism
multiples of its generator. -/
theorem exists_postcomposition_of_mem_twoSidedEndomorphismSpan
    {X Y : C} {f g : X ⟶ Y} (ht : AllowsTransit f)
    (hg : g ∈ twoSidedEndomorphismSpan (k := k) f) :
    ∃ b : End Y, g = f ≫ b.asHom := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht a
      refine ⟨b * c, ?_⟩
      rw [hc, End.mul_def, Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = f ≫ (0 : Y ⟶ Y)
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (f ≫ a.asHom) + (f ≫ b.asHom) =
        f ≫ (a.asHom + b.asHom)
      rw [Preadditive.comp_add]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (f ≫ a.asHom) = f ≫ (c • a.asHom)
      rw [Linear.comp_smul]

/-- Cotransit collapses a principal two-sided span to source-endomorphism
multiples of its generator. -/
theorem exists_precomposition_of_mem_twoSidedEndomorphismSpan
    {X Y : C} {f g : X ⟶ Y} (hc : AllowsCotransit f)
    (hg : g ∈ twoSidedEndomorphismSpan (k := k) f) :
    ∃ a : End X, g = a.asHom ≫ f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := hc b
      refine ⟨a.asHom ≫ c.asHom, ?_⟩
      change (a.asHom ≫ f) ≫ b.asHom =
        (a.asHom ≫ c.asHom) ≫ f
      rw [Category.assoc, hc]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = (0 : X ⟶ X) ≫ f
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (a.asHom ≫ f) + (b.asHom ≫ f) =
        (a.asHom + b.asHom) ≫ f
      rw [Preadditive.add_comp]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (a.asHom ≫ f) = (c • a.asHom) ≫ f
      rw [Linear.smul_comp]

private theorem twoSidedEndomorphismSpan_zero
    {X Y : C} :
    twoSidedEndomorphismSpan (k := k) (0 : X ⟶ Y) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro g ⟨a, b, rfl⟩
    simp
  · exact bot_le

/-- A finite-dimensional endpoint-stable subspace whose endpoint-stable
subspaces are comparable has a single two-sided generator. -/
theorem exists_twoSidedEndomorphismSpan_eq
    {X Y : C} [Module.Finite k (X ⟶ Y)]
    (T : Submodule k (X ⟶ Y)) (hT : IsHomSubbimodule T)
    (hcomparable : ∀ (U V : Submodule k (X ⟶ Y)),
      IsHomSubbimodule U → IsHomSubbimodule V → U ≤ V ∨ V ≤ U) :
    ∃ f : X ⟶ Y,
      f ∈ T ∧ twoSidedEndomorphismSpan (k := k) f = T := by
  classical
  by_cases hTzero : Module.finrank k T = 0
  · have hTbot : T = ⊥ := Submodule.finrank_eq_zero.mp hTzero
    refine ⟨0, T.zero_mem, ?_⟩
    rw [twoSidedEndomorphismSpan_zero, hTbot]
  · let b := Module.finBasis k T
    have hnonempty : Nonempty (Fin (Module.finrank k T)) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hTzero)
    obtain ⟨i, _hi, himax⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin (Module.finrank k T)))
      (fun j ↦ Module.finrank k
        (twoSidedEndomorphismSpan (k := k) (b j).1))
      ⟨Classical.choice hnonempty, Finset.mem_univ _⟩
    let F : X ⟶ Y := (b i).1
    have hspan_le (j : Fin (Module.finrank k T)) :
        twoSidedEndomorphismSpan (k := k) (b j).1 ≤ T := by
      apply Submodule.span_le.2
      rintro g ⟨a, c, rfl⟩
      exact hT.2 c (hT.1 a (b j).2)
    have hbasis_mem (j : Fin (Module.finrank k T)) :
        (b j).1 ∈ twoSidedEndomorphismSpan (k := k) F := by
      rcases hcomparable
          (twoSidedEndomorphismSpan (k := k) (b j).1)
          (twoSidedEndomorphismSpan (k := k) F)
          (isHomSubbimodule_twoSidedEndomorphismSpan (k := k) (b j).1)
          (isHomSubbimodule_twoSidedEndomorphismSpan (k := k) F) with hji | hij
      · exact hji (mem_twoSidedEndomorphismSpan (k := k) (b j).1)
      · have hdim : Module.finrank k
            (twoSidedEndomorphismSpan (k := k) (b j).1) ≤
            Module.finrank k
              (twoSidedEndomorphismSpan (k := k) F) :=
          himax j (Finset.mem_univ _)
        have heq : twoSidedEndomorphismSpan (k := k) F =
            twoSidedEndomorphismSpan (k := k) (b j).1 := by
          apply Submodule.eq_of_le_of_finrank_eq hij
          exact le_antisymm
            (LinearMap.finrank_le_finrank_of_injective
              (Submodule.inclusion_injective hij)) hdim
        rw [heq]
        exact mem_twoSidedEndomorphismSpan (k := k) (b j).1
    refine ⟨F, (b i).2, le_antisymm (hspan_le i) ?_⟩
    intro g hg
    let gt : T := ⟨g, hg⟩
    have htop : (⊤ : Submodule k T) ≤
        (twoSidedEndomorphismSpan (k := k) F).comap T.subtype := by
      rw [← b.span_eq]
      apply Submodule.span_le.2
      rintro x ⟨j, rfl⟩
      exact hbasis_mem j
    exact htop (show gt ∈ (⊤ : Submodule k T) from Submodule.mem_top)

/-- The algebraically closed residue map supplies the hypotheses of the
generic Kupisch cyclicity theorem. -/
theorem transit_or_cotransit_of_homSubbimodule_comparable_local
    [IsAlgClosed k] {X Y : C}
    [Module.Finite k (End X)] [Module.Finite k (End Y)]
    [IsLocalRing (End X)] [IsLocalRing (End Y)]
    (f : X ⟶ Y)
    (hcomparable : ∀ (U V : Submodule k (X ⟶ Y)),
      IsHomSubbimodule U → IsHomSubbimodule V → U ≤ V ∨ V ≤ U) :
    AllowsTransit f ∨ AllowsCotransit f := by
  letI : IsArtinianRing (End X) := IsArtinianRing.of_finite k (End X)
  letI : IsArtinianRing (End Y) := IsArtinianRing.of_finite k (End Y)
  apply transit_or_cotransit_of_homSubbimodule_comparable
    (k := k) f
    (LocalAlgebraResidue.residueAlgHom k (End X))
    (LocalAlgebraResidue.residueAlgHom k (End Y))
  · intro a
    rw [LocalAlgebraResidue.residueAlgHom_apply,
      ← LocalAlgebraResidue.residueLinearMap_apply,
      ← LinearMap.mem_ker]
    exact (LocalAlgebraResidue.mem_ker_residueLinearMap_iff a).trans
      (mem_ringJacobson_iff_not_isUnit (End X) a).symm
  · intro b
    rw [LocalAlgebraResidue.residueAlgHom_apply,
      ← LocalAlgebraResidue.residueLinearMap_apply,
      ← LinearMap.mem_ker]
    exact (LocalAlgebraResidue.mem_ker_residueLinearMap_iff b).trans
      (mem_ringJacobson_iff_not_isUnit (End Y) b).symm
  · exact hcomparable

private theorem algebra_adjoin_singleton_eq_top_of_left_radical_generator
    [IsAlgClosed k] {R : Type v} [Ring R] [Algebra k R]
    [Module.Finite k R] [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ q : R, x = q * tau) :
    Algebra.adjoin k ({tau} : Set R) = ⊤ := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  have htauN : tau ^ N = 0 := by
    have htauPow : tau ^ N ∈ (Ring.jacobson R) ^ N :=
      Ideal.pow_mem_pow htauJ N
    rw [hN] at htauPow
    simpa using htauPow
  let S : Subalgebra k R := Algebra.adjoin k ({tau} : Set R)
  have htauS : tau ∈ S := Algebra.self_mem_adjoin_singleton k tau
  have hiter : ∀ (n : ℕ) (x : R),
      ∃ s : R, s ∈ S ∧ ∃ q : R, x = s + q * tau ^ n := by
    intro n
    induction n with
    | zero =>
        intro x
        exact ⟨0, S.zero_mem, x, by simp⟩
    | succ n ih =>
        intro x
        obtain ⟨s, hs, q, hx⟩ := ih x
        let c : k := LocalAlgebraResidue.residueScalar k q
        have hcJ : q - algebraMap k R c ∈ Ring.jacobson R := by
          apply (mem_ringJacobson_iff_not_isUnit R _).2
          exact LocalAlgebraResidue.residueScalar_spec q
        obtain ⟨r, hr⟩ := hgen (q - algebraMap k R c) hcJ
        have hq : q = algebraMap k R c + r * tau := by
          calc
            q = (q - algebraMap k R c) + algebraMap k R c :=
              (sub_add_cancel q (algebraMap k R c)).symm
            _ = r * tau + algebraMap k R c := by rw [hr]
            _ = algebraMap k R c + r * tau := add_comm _ _
        refine ⟨s + algebraMap k R c * tau ^ n,
          S.add_mem hs (S.mul_mem (S.algebraMap_mem c) (S.pow_mem htauS n)),
          r, ?_⟩
        calc
          x = s + q * tau ^ n := hx
          _ = s + (algebraMap k R c + r * tau) * tau ^ n := by rw [hq]
          _ = (s + algebraMap k R c * tau ^ n) +
              r * tau ^ (n + 1) := by
            rw [add_mul, mul_assoc, ← pow_succ']
            exact (add_assoc s (algebraMap k R c * tau ^ n)
              (r * tau ^ (n + 1))).symm
  apply top_unique
  intro x _hx
  obtain ⟨s, hs, q, hx⟩ := hiter N x
  rw [htauN, mul_zero, add_zero] at hx
  simpa [S, hx] using hs

private theorem algebra_adjoin_singleton_eq_top_of_right_radical_generator
    [IsAlgClosed k] {R : Type v} [Ring R] [Algebra k R]
    [Module.Finite k R] [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ q : R, x = tau * q) :
    Algebra.adjoin k ({tau} : Set R) = ⊤ := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  have htauN : tau ^ N = 0 := by
    have htauPow : tau ^ N ∈ (Ring.jacobson R) ^ N :=
      Ideal.pow_mem_pow htauJ N
    rw [hN] at htauPow
    simpa using htauPow
  let S : Subalgebra k R := Algebra.adjoin k ({tau} : Set R)
  have htauS : tau ∈ S := Algebra.self_mem_adjoin_singleton k tau
  have hiter : ∀ (n : ℕ) (x : R),
      ∃ s : R, s ∈ S ∧ ∃ q : R, x = s + tau ^ n * q := by
    intro n
    induction n with
    | zero =>
        intro x
        exact ⟨0, S.zero_mem, x, by simp⟩
    | succ n ih =>
        intro x
        obtain ⟨s, hs, q, hx⟩ := ih x
        let c : k := LocalAlgebraResidue.residueScalar k q
        have hcJ : q - algebraMap k R c ∈ Ring.jacobson R := by
          apply (mem_ringJacobson_iff_not_isUnit R _).2
          exact LocalAlgebraResidue.residueScalar_spec q
        obtain ⟨r, hr⟩ := hgen (q - algebraMap k R c) hcJ
        have hq : q = algebraMap k R c + tau * r := by
          calc
            q = (q - algebraMap k R c) + algebraMap k R c :=
              (sub_add_cancel q (algebraMap k R c)).symm
            _ = tau * r + algebraMap k R c := by rw [hr]
            _ = algebraMap k R c + tau * r := add_comm _ _
        refine ⟨s + tau ^ n * algebraMap k R c,
          S.add_mem hs (S.mul_mem (S.pow_mem htauS n) (S.algebraMap_mem c)),
          r, ?_⟩
        calc
          x = s + tau ^ n * q := hx
          _ = s + tau ^ n * (algebraMap k R c + tau * r) := by rw [hq]
          _ = (s + tau ^ n * algebraMap k R c) +
              tau ^ (n + 1) * r := by
            rw [mul_add, ← mul_assoc, ← pow_succ]
            exact (add_assoc s (tau ^ n * algebraMap k R c)
              (tau ^ (n + 1) * r)).symm
  apply top_unique
  intro x _hx
  obtain ⟨s, hs, q, hx⟩ := hiter N x
  rw [htauN, zero_mul, add_zero] at hx
  simpa [S, hx] using hs

private theorem commute_of_adjoin_singleton_eq_top
    {R : Type v} [Ring R] [Algebra k R] (tau : R)
    (hgen : Algebra.adjoin k ({tau} : Set R) = ⊤) (a b : R) :
    Commute a b := by
  have ha : a ∈ Algebra.adjoin k ({tau} : Set R) := by
    rw [hgen]
    trivial
  have hb : b ∈ Algebra.adjoin k ({tau} : Set R) := by
    rw [hgen]
    trivial
  exact Algebra.commute_of_mem_adjoin_singleton_of_commute hb
    (Algebra.commute_of_mem_adjoin_self ha).symm

private theorem exists_left_unit_times_power
    {R : Type v} [Ring R] [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ y : R, x = y * tau)
    {x : R} (hxJ : x ∈ Ring.jacobson R) (hx0 : x ≠ 0) :
    ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = u * tau ^ n := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  have hiter : ∀ n : ℕ,
      (∃ m : ℕ, m ≤ n ∧ ∃ u : R, IsUnit u ∧ x = u * tau ^ m) ∨
      (∃ y : R, y ∈ Ring.jacobson R ∧ x = y * tau ^ n) := by
    intro n
    induction n with
    | zero => exact Or.inr ⟨x, hxJ, by simp⟩
    | succ n ih =>
        rcases ih with hdone | ⟨y, hyJ, hxy⟩
        · left
          rcases hdone with ⟨m, hmn, u, hu, hxu⟩
          exact ⟨m, hmn.trans (Nat.le_succ n), u, hu, hxu⟩
        · obtain ⟨q, hyq⟩ := hgen y hyJ
          by_cases hq : IsUnit q
          · left
            refine ⟨n + 1, Nat.le_refl _, q, hq, ?_⟩
            rw [hyq] at hxy
            calc
              x = (q * tau) * tau ^ n := hxy
              _ = q * tau ^ (n + 1) := by
                rw [pow_succ']
                exact mul_assoc _ _ _
          · right
            refine ⟨q, (mem_ringJacobson_iff_not_isUnit R q).2 hq, ?_⟩
            rw [hyq] at hxy
            calc
              x = (q * tau) * tau ^ n := hxy
              _ = q * tau ^ (n + 1) := by
                rw [pow_succ']
                exact mul_assoc _ _ _
  rcases hiter N with hdone | ⟨y, _hyJ, hxy⟩
  · rcases hdone with ⟨n, _hnN, u, hu, hxu⟩
    exact ⟨n, u, hu, hxu⟩
  · have htauPow : tau ^ N = 0 := by
      have htauPowMem : tau ^ N ∈ (Ring.jacobson R) ^ N :=
        Ideal.pow_mem_pow htauJ N
      rw [hN] at htauPowMem
      simpa using htauPowMem
    exact (hx0 (by rw [hxy, htauPow, mul_zero])).elim

private theorem isUniserialModule_self_of_all_nonzero_isUnit
    {R : Type v} [Ring R]
    (hunit : ∀ x : R, x ≠ 0 → IsUnit x) :
    IsUniserialModule R R := by
  apply IsUniserialModule.of_smul_comparable
  intro x y
  by_cases hx : x = 0
  · right
    refine ⟨0, ?_⟩
    simp [hx]
  · left
    let u := (hunit x hx).unit
    refine ⟨y * (↑(u⁻¹) : R), ?_⟩
    change (y * (↑(u⁻¹) : R)) * x = y
    rw [show x = (u : R) by exact (hunit x hx).unit_spec.symm,
      mul_assoc, Units.inv_mul, mul_one]

private theorem isUniserialModule_self_of_left_power_normalForm
    {R : Type v} [Ring R] [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ y : R, x = y * tau) :
    IsUniserialModule R R := by
  apply IsUniserialModule.of_smul_comparable
  intro x y
  by_cases hx : x = 0
  · right
    refine ⟨0, by simp [hx]⟩
  by_cases hy : y = 0
  · left
    refine ⟨0, by simp [hy]⟩
  by_cases hxU : IsUnit x
  · left
    let u := hxU.unit
    refine ⟨y * (↑(u⁻¹) : R), ?_⟩
    change (y * (↑(u⁻¹) : R)) * x = y
    rw [show x = (u : R) by exact hxU.unit_spec.symm,
      mul_assoc, Units.inv_mul, mul_one]
  by_cases hyU : IsUnit y
  · right
    let u := hyU.unit
    refine ⟨x * (↑(u⁻¹) : R), ?_⟩
    change (x * (↑(u⁻¹) : R)) * y = x
    rw [show y = (u : R) by exact hyU.unit_spec.symm,
      mul_assoc, Units.inv_mul, mul_one]
  have hxJ : x ∈ Ring.jacobson R :=
    (mem_ringJacobson_iff_not_isUnit R x).2 hxU
  have hyJ : y ∈ Ring.jacobson R :=
    (mem_ringJacobson_iff_not_isUnit R y).2 hyU
  obtain ⟨m, e, he, hxe⟩ :=
    exists_left_unit_times_power tau htauJ hgen hxJ hx
  obtain ⟨n, f, hf, hyf⟩ :=
    exists_left_unit_times_power tau htauJ hgen hyJ hy
  rcases le_total m n with hmn | hnm
  · left
    let einv : R := ↑(he.unit⁻¹)
    refine ⟨f * tau ^ (n - m) * einv, ?_⟩
    change (f * tau ^ (n - m) * einv) * x = y
    rw [hxe, hyf]
    calc
      (f * tau ^ (n - m) * einv) * (e * tau ^ m) =
          f * tau ^ (n - m) * (einv * e) * tau ^ m := by
            simp only [mul_assoc]
      _ = f * (tau ^ (n - m) * tau ^ m) := by
            rw [show einv * e = 1 by
              exact Units.inv_mul he.unit]
            simp only [mul_one, mul_assoc]
      _ = f * tau ^ n := by
            rw [← pow_add, Nat.sub_add_cancel hmn]
  · right
    let finv : R := ↑(hf.unit⁻¹)
    refine ⟨e * tau ^ (m - n) * finv, ?_⟩
    change (e * tau ^ (m - n) * finv) * y = x
    rw [hxe, hyf]
    calc
      (e * tau ^ (m - n) * finv) * (f * tau ^ n) =
          e * tau ^ (m - n) * (finv * f) * tau ^ n := by
            simp only [mul_assoc]
      _ = e * (tau ^ (m - n) * tau ^ n) := by
            rw [show finv * f = 1 by
              exact Units.inv_mul hf.unit]
            simp only [mul_one, mul_assoc]
      _ = e * tau ^ m := by
            rw [← pow_add, Nat.sub_add_cancel hnm]

private theorem isUniserialModule_opposite_self_of_commute
    {R : Type v} [Ring R]
    (hR : IsUniserialModule R R)
    (hcomm : ∀ a b : R, a * b = b * a) :
    IsUniserialModule Rᵐᵒᵖ Rᵐᵒᵖ := by
  apply IsUniserialModule.of_smul_comparable
  intro x y
  rcases hR.smul_comparable x.unop y.unop with hxy | hyx
  · left
    obtain ⟨r, hr⟩ := hxy
    change r * x.unop = y.unop at hr
    refine ⟨MulOpposite.op r, ?_⟩
    apply MulOpposite.unop_injective
    change x.unop * r = y.unop
    rw [hcomm, hr]
  · right
    obtain ⟨r, hr⟩ := hyx
    change r * y.unop = x.unop at hr
    refine ⟨MulOpposite.op r, ?_⟩
    apply MulOpposite.unop_injective
    change y.unop * r = x.unop
    rw [hcomm, hr]

/-- Comparable endomorphism subbimodules make both regular endpoint modules
uniserial.  The zero-radical case is division-like; otherwise a maximal
radical generator, Kupisch orientation, and polynomial generation give the
power normal form. -/
theorem end_regular_and_opposite_uniserial_of_homSubbimodule_comparable
    [IsAlgClosed k] (X : C)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (End X)]
    [IsLocalRing (End X)]
    (hcomparable : ∀ (U V : Submodule k (End X)),
      IsHomSubbimodule U → IsHomSubbimodule V → U ≤ V ∨ V ≤ U) :
    IsUniserialModule (End X) (End X) ∧
      IsUniserialModule (End X)ᵐᵒᵖ (End X)ᵐᵒᵖ := by
  letI : IsArtinianRing (End X) := IsArtinianRing.of_finite k (End X)
  let J : Submodule k (End X) :=
    (Ring.jacobson (End X)).restrictScalars k
  have hJ : IsHomSubbimodule J := by
    constructor
    · intro a f hf
      change (show End X from f) * a ∈ Ring.jacobson (End X)
      exact (Ring.jacobson (End X)).mul_mem_right a hf
    · intro b f hf
      change b * (show End X from f) ∈ Ring.jacobson (End X)
      exact (Ring.jacobson (End X)).mul_mem_left b hf
  obtain ⟨tauHom, htauJ, htauSpan⟩ :=
    exists_twoSidedEndomorphismSpan_eq (k := k) J hJ hcomparable
  let tau : End X := End.of tauHom
  by_cases hJzero : Ring.jacobson (End X) = ⊥
  · have hunit : ∀ x : End X, x ≠ 0 → IsUnit x := by
      intro x hx
      by_contra hnonunit
      have hxJ : x ∈ Ring.jacobson (End X) :=
        (mem_ringJacobson_iff_not_isUnit (End X) x).2 hnonunit
      rw [hJzero] at hxJ
      exact hx ((Submodule.mem_bot (R := End X)).1 hxJ)
    have hself := isUniserialModule_self_of_all_nonzero_isUnit hunit
    have hop : IsUniserialModule (End X)ᵐᵒᵖ (End X)ᵐᵒᵖ := by
      apply isUniserialModule_self_of_all_nonzero_isUnit
      intro x hx
      apply (isUnit_unop).mp
      apply hunit x.unop
      exact fun h ↦ hx (MulOpposite.unop_injective h)
    exact ⟨hself, hop⟩
  · have htau0 : tauHom ≠ 0 := by
      intro htau
      have hspan0 : twoSidedEndomorphismSpan (k := k) tauHom = ⊥ := by
        rw [htau]
        exact twoSidedEndomorphismSpan_zero
      have hJbot : J = ⊥ := htauSpan.symm.trans hspan0
      apply hJzero
      ext x
      change x ∈ J ↔ x ∈ (⊥ : Submodule k (End X))
      rw [hJbot]
    have htauJ' : tau ∈ Ring.jacobson (End X) := htauJ
    have horient : AllowsTransit tauHom ∨ AllowsCotransit tauHom :=
      transit_or_cotransit_of_homSubbimodule_comparable_local
        (k := k) tauHom hcomparable
    have hleftOrRight :
        (∀ x : End X, x ∈ Ring.jacobson (End X) →
          ∃ q : End X, x = q * tau) ∨
        (∀ x : End X, x ∈ Ring.jacobson (End X) →
          ∃ q : End X, x = tau * q) := by
      rcases horient with hT | hC
      · left
        intro x hx
        have hxspan : x ∈ twoSidedEndomorphismSpan (k := k) tauHom := by
          rw [htauSpan]
          exact hx
        obtain ⟨q, hq⟩ :=
          exists_postcomposition_of_mem_twoSidedEndomorphismSpan hT hxspan
        refine ⟨q, ?_⟩
        change x.asHom = (q * tau).asHom
        simpa only [End.mul_def] using hq
      · right
        intro x hx
        have hxspan : x ∈ twoSidedEndomorphismSpan (k := k) tauHom := by
          rw [htauSpan]
          exact hx
        obtain ⟨q, hq⟩ :=
          exists_precomposition_of_mem_twoSidedEndomorphismSpan hC hxspan
        refine ⟨q, ?_⟩
        change x.asHom = (tau * q).asHom
        simpa only [End.mul_def] using hq
    have hadjoin : Algebra.adjoin k ({tau} : Set (End X)) = ⊤ := by
      rcases hleftOrRight with hleft | hright
      · exact algebra_adjoin_singleton_eq_top_of_left_radical_generator
          tau htauJ' hleft
      · exact algebra_adjoin_singleton_eq_top_of_right_radical_generator
          tau htauJ' hright
    have hcomm : ∀ a b : End X, a * b = b * a := fun a b ↦
      (commute_of_adjoin_singleton_eq_top tau hadjoin a b).eq
    have hleft : ∀ x : End X, x ∈ Ring.jacobson (End X) →
        ∃ q : End X, x = q * tau := by
      rcases hleftOrRight with h | h
      · exact h
      · intro x hx
        obtain ⟨q, hq⟩ := h x hx
        exact ⟨q, hq.trans (hcomm tau q)⟩
    have hself : IsUniserialModule (End X) (End X) :=
      isUniserialModule_self_of_left_power_normalForm tau htauJ' hleft
    exact ⟨hself,
      isUniserialModule_opposite_self_of_commute hself hcomm⟩

/-- Kupisch's condition (K)(2): in a finite-dimensional linear category with
local endpoints and comparable Hom subbimodules, every Hom space is uniserial
as a module over its target endomorphism ring or over the opposite of its
source endomorphism ring. -/
theorem uniserialModule_or_opposite_of_homSubbimodule_comparable
    [IsAlgClosed k]
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, Module.Finite k (End X)]
    [∀ X : C, IsLocalRing (End X)]
    (hcomparable : ∀ {X Y : C} (U V : Submodule k (X ⟶ Y)),
      IsHomSubbimodule U → IsHomSubbimodule V → U ≤ V ∨ V ≤ U)
    (X Y : C) :
    IsUniserialModule (End Y) (X ⟶ Y) ∨
      IsUniserialModule (End X)ᵐᵒᵖ (X ⟶ Y) := by
  have htop : IsHomSubbimodule (⊤ : Submodule k (X ⟶ Y)) := by
    constructor <;> intro <;> simp
  obtain ⟨pi, _hpi, hpiSpan⟩ :=
    exists_twoSidedEndomorphismSpan_eq (k := k)
      (⊤ : Submodule k (X ⟶ Y)) htop hcomparable
  have hY :=
    end_regular_and_opposite_uniserial_of_homSubbimodule_comparable
      (k := k) Y (fun U V hU hV ↦ hcomparable U V hU hV)
  have hX :=
    end_regular_and_opposite_uniserial_of_homSubbimodule_comparable
      (k := k) X (fun U V hU hV ↦ hcomparable U V hU hV)
  rcases transit_or_cotransit_of_homSubbimodule_comparable_local
      (k := k) pi (fun U V hU hV ↦ hcomparable U V hU hV) with hT | hC
  · left
    apply hY.1.of_surjective
      (LinearMap.toSpanSingleton (End Y) (X ⟶ Y) pi)
    intro g
    have hgspan : g ∈ twoSidedEndomorphismSpan (k := k) pi := by
      rw [hpiSpan]
      exact Submodule.mem_top
    obtain ⟨b, hgb⟩ :=
      exists_postcomposition_of_mem_twoSidedEndomorphismSpan hT hgspan
    refine ⟨b, ?_⟩
    change b • pi = g
    change pi ≫ b.asHom = g
    exact hgb.symm
  · right
    apply hX.2.of_surjective
      (LinearMap.toSpanSingleton (End X)ᵐᵒᵖ (X ⟶ Y) pi)
    intro g
    have hgspan : g ∈ twoSidedEndomorphismSpan (k := k) pi := by
      rw [hpiSpan]
      exact Submodule.mem_top
    obtain ⟨a, hga⟩ :=
      exists_precomposition_of_mem_twoSidedEndomorphismSpan hC hgspan
    refine ⟨MulOpposite.op a, ?_⟩
    change MulOpposite.op a • pi = g
    change a.asHom ≫ pi = g
    exact hga.symm

end MagnitudeConjecture
