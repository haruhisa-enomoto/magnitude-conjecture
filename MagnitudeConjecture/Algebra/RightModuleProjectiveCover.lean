import MagnitudeConjecture.Algebra.RightModuleLeftAlmostSplit
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.ProjectiveCover
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Artinian.Module

/-!
# Minimal finite projective presentations

Ringel's construction of the Auslander--Reiten translate starts from a
minimal projective presentation.  This file supplies the first step: over a
finite-dimensional algebra, every finitely generated module admits a
right-minimal epimorphism from a finitely generated projective module.

The proof starts with a finite free epimorphism and minimizes the scalar
dimension of its projective source.  If an endomorphism fixing such an
epimorphism were not invertible, Fitting decomposition would replace its
source by a proper projective stable image, contradicting minimality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- The scalar dimension of the projective source of a presentation. -/
private def projectivePresentationFinrank
    (k : Type u) [Field k] [Algebra k R]
    {X : FGModuleCat.{u} R} (P : ProjectivePresentation X) : ℕ := by
  letI : Module k P.p := Module.restrictScalars k R P.p
  exact Module.finrank k P.p

omit [IsNoetherianRing R] in
/-- Powers of an endomorphism fixing an epimorphism still fix it. -/
private theorem pow_comp_eq
    {P X : FGModuleCat.{u} R} (e : P ⟶ P) (q : P ⟶ X)
    (he : e ≫ q = q) (n : ℕ) :
    q.hom.hom.comp (e.hom.hom ^ n) = q.hom.hom := by
  induction n with
  | zero =>
      ext x
      rfl
  | succ n ih =>
      ext x
      have heApply := congrArg (fun f : P ⟶ X ↦ f.hom.hom x) he
      change q.hom.hom (e.hom.hom x) = q.hom.hom x at heApply
      change q.hom.hom ((e.hom.hom ^ (n + 1)) x) = q.hom.hom x
      rw [pow_succ]
      change q.hom.hom ((e.hom.hom ^ n) (e.hom.hom x)) = _
      exact (LinearMap.congr_fun ih (e.hom.hom x)).trans heApply

/-- A noninvertible finite-dimensional endomorphism has proper range in
every positive power. -/
private theorem range_pow_ne_top_of_not_isIso
    {P : FGModuleCat.{u} R} (e : P ⟶ P) (hnot : ¬ IsIso e)
    {n : ℕ} (hn : 0 < n) :
    LinearMap.range (e.hom.hom ^ n) ≠ ⊤ := by
  intro hrange
  have hpowSurjective : Function.Surjective (e.hom.hom ^ n) :=
    LinearMap.range_eq_top.mp hrange
  have heSurjective : Function.Surjective e.hom.hom := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    intro y
    obtain ⟨x, hx⟩ := hpowSurjective y
    refine ⟨(e.hom.hom ^ m) x, ?_⟩
    simpa [pow_succ'] using hx
  have heInjective : Function.Injective e.hom.hom := by
    exact IsNoetherian.injective_of_surjective_endomorphism
      e.hom.hom heSurjective
  apply hnot
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  haveI : IsIso (U.map e) := by
    change IsIso e.hom
    exact (ConcreteCategory.isIso_iff_bijective e.hom).2
      ⟨heInjective, heSurjective⟩
  exact isIso_of_reflects_iso e U

/-- The stable range in a Fitting decomposition is a projective module when
the ambient module is projective. -/
private theorem projective_range_pow
    {P : FGModuleCat.{u} R} (hP : Projective P) (e : P ⟶ P)
    {n : ℕ}
    (hcompl : IsCompl (LinearMap.ker (e.hom.hom ^ n))
      (LinearMap.range (e.hom.hom ^ n))) :
    Module.Projective R (LinearMap.range (e.hom.hom ^ n)) := by
  letI : Projective P := hP
  letI : Module.Projective R P :=
    moduleProjective_of_fgProjective P hP
  let Q := LinearMap.range (e.hom.hom ^ n)
  let projection : P →ₗ[R] Q :=
    Q.projectionOnto (LinearMap.ker (e.hom.hom ^ n)) hcompl.symm
  apply Module.Projective.of_split Q.subtype projection
  ext x
  exact congrArg Subtype.val
    (Submodule.projectionOnto_apply_left hcompl.symm x)

/-- Every finitely generated module over a finite-dimensional algebra has a
minimal finite projective presentation. -/
theorem minimalProjectivePresentation_nonempty
    (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R]
    (X : FGModuleCat.{u} R) :
    Nonempty (MinimalProjectivePresentation X) := by
  classical
  let Candidate : ℕ → Prop := fun n ↦
    ∃ P : ProjectivePresentation X,
      projectivePresentationFinrank k P = n
  have hCandidate : ∃ n, Candidate n := by
    obtain ⟨P⟩ := fgModuleCat_projectivePresentation_nonempty X
    exact ⟨projectivePresentationFinrank k P, P, rfl⟩
  let n := Nat.find hCandidate
  obtain ⟨P, hPfinrank⟩ := Nat.find_spec hCandidate
  refine ⟨{
    toProjectivePresentation := P
    rightMinimal := ?_ }⟩
  intro e he
  by_contra hnotIso
  let f : Module.End R P.p := e.hom.hom
  have hfiniteLength : IsFiniteLength R P.p := by
    letI : IsArtinianRing R := IsArtinianRing.of_finite k R
    exact ((IsArtinianRing.tfae R P.p).out 0 3).mp
      (inferInstance : Module.Finite R P.p)
  letI : IsNoetherian R P.p :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
  letI : IsArtinian R P.p :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp
      (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  let m := max N 1
  have hmN : N ≤ m := le_max_left _ _
  have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hcompl : IsCompl (LinearMap.ker (f ^ m))
      (LinearMap.range (f ^ m)) := hN m hmN
  let QModule := LinearMap.range (f ^ m)
  let Q : FGModuleCat.{u} R := FGModuleCat.of R QModule
  have hQProjectiveModule : Module.Projective R QModule :=
    projective_range_pow P.projective e hcompl
  have hQProjective : Projective Q :=
    fgProjective_of_moduleProjective Q hQProjectiveModule
  let inclusion : Q ⟶ P.p := FGModuleCat.ofHom QModule.subtype
  let q : Q ⟶ X := inclusion ≫ P.f
  have hqSurjective : Function.Surjective q.hom.hom := by
    have hPSurjective : Function.Surjective P.f.hom.hom :=
      (IndecomposableSkeleton.fg_epi_iff_surjective P.f).1 inferInstance
    intro x
    obtain ⟨p, hp⟩ := hPSurjective x
    let y : QModule := ⟨(f ^ m) p, LinearMap.mem_range_self (f ^ m) p⟩
    refine ⟨y, ?_⟩
    change P.f.hom.hom ((f ^ m) p) = x
    have hfix := LinearMap.congr_fun (pow_comp_eq e P.f he m) p
    exact hfix.trans hp
  have hqEpi : Epi q :=
    (IndecomposableSkeleton.fg_epi_iff_surjective q).2 hqSurjective
  let QPresentation : ProjectivePresentation X :=
    { p := Q
      projective := hQProjective
      f := q
      epi := hqEpi }
  have hQProper : QModule ≠ ⊤ := by
    exact range_pow_ne_top_of_not_isIso e hnotIso hmPos
  letI : Module k P.p := Module.restrictScalars k R P.p
  letI : IsScalarTower k R P.p :=
    IsScalarTower.restrictScalars k R P.p
  letI : Module.Finite k P.p := Module.Finite.trans R P.p
  letI : FiniteDimensional k P.p :=
    inferInstance
  have hQfinrank : Module.finrank k QModule < Module.finrank k P.p := by
    let W : Submodule k P.p := QModule.restrictScalars k
    have hWProper : W ≠ ⊤ := by
      simpa [W] using hQProper
    exact Submodule.finrank_lt hWProper
  have hminimal : n ≤ projectivePresentationFinrank k QPresentation :=
    Nat.find_min' hCandidate ⟨QPresentation, rfl⟩
  change Module.finrank k P.p = n at hPfinrank
  change n ≤ Module.finrank k QModule at hminimal
  rw [← hPfinrank] at hminimal
  exact (Nat.not_lt_of_ge hminimal) hQfinrank

/-- Two-step minimal projective presentations exist over every
finite-dimensional algebra. -/
theorem twoStepMinimalProjectivePresentation_nonempty
    (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R]
    (X : FGModuleCat.{u} R) :
    Nonempty (TwoStepMinimalProjectivePresentation X) := by
  obtain ⟨P₀⟩ := minimalProjectivePresentation_nonempty k X
  obtain ⟨P₁⟩ :=
    minimalProjectivePresentation_nonempty k (kernel P₀.f)
  exact ⟨{ augmentation := P₀, syzygyPresentation := P₁ }⟩

namespace TwoStepMinimalProjectivePresentation

variable {X : FGModuleCat.{u} R}

/-- If the first differential in a two-step minimal presentation is monic,
then the presented module has projective dimension at most one. -/
theorem hasProjectiveDimensionLE_one_of_mono_differential
    (P : TwoStepMinimalProjectivePresentation X)
    (hmono : Mono P.differential) :
    HasProjectiveDimensionLE X 1 := by
  letI : Mono P.presentationComplex.f := by
    dsimp [presentationComplex]
    exact hmono
  letI : Projective P.presentationComplex.X₁ := by
    dsimp [presentationComplex]
    infer_instance
  letI : Projective P.presentationComplex.X₂ := by
    dsimp [presentationComplex]
    infer_instance
  letI : Epi P.presentationComplex.g := by
    dsimp [presentationComplex]
    infer_instance
  have hshort : P.presentationComplex.ShortExact :=
    { exact := P.presentationComplex_exact }
  exact hshort.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

end TwoStepMinimalProjectivePresentation

end MagnitudeConjecture
