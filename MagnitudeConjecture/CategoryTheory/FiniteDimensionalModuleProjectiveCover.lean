import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import Mathlib.RingTheory.Artinian.Module
import QuotientSubmoduleEquidistribution.CategoryTheory.SplitMorphismComplement

/-!
# Minimal projective covers of finite-dimensional modules

An endomorphism of a finite-support pointwise finite-dimensional module has a
uniform stable image.  The induced endomorphism of that image is invertible,
so a noninvertible endomorphism of a projective object exhibits a strictly
smaller projective retract.  Minimizing total dimension among projective
presentations therefore produces a right-minimal projective epimorphism.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

private def endomorphismPower
    {X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (e : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => e ≫ endomorphismPower e n

@[simp]
private theorem endomorphismPower_app_hom
    {X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (e : X ⟶ X) (n : ℕ) (Y : C) :
    ((endomorphismPower e n).hom.hom.app Y).hom =
      (e.hom.hom.app Y).hom ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((endomorphismPower e n).hom.hom.app Y).hom.comp
          (e.hom.hom.app Y).hom = _
      rw [ih, pow_succ]
      rfl

private theorem endomorphismPower_succ_right
    {X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (e : X ⟶ X) (n : ℕ) :
    endomorphismPower e (n + 1) = endomorphismPower e n ≫ e := by
  induction n with
  | zero => simp [endomorphismPower]
  | succ n ih =>
      have ih' : e ≫ endomorphismPower e n =
          endomorphismPower e n ≫ e := by
        simpa only [endomorphismPower] using ih
      simp only [endomorphismPower, Category.assoc]
      rw [ih']

private theorem endomorphismPower_comp_eq
    {P X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (e : P ⟶ P) (f : P ⟶ X) (he : e ≫ f = f) (n : ℕ) :
    endomorphismPower e n ≫ f = f := by
  induction n with
  | zero => simp [endomorphismPower]
  | succ n ih =>
      simp only [endomorphismPower, Category.assoc]
      rw [ih, he]

private theorem exists_uniform_range_pow_stable
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (e : M ⟶ M) :
    ∃ n : ℕ, 0 < n ∧ ∀ X : moduleSupport k M.obj.obj,
      LinearMap.range ((e.hom.hom.app X.1).hom ^ n) =
        LinearMap.range ((e.hom.hom.app X.1).hom ^ (2 * n)) := by
  classical
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := M.property.2.fintype
  have hstabilizes (X : S) :
      ∃ b : ℕ, ∀ m, b ≤ m →
        LinearMap.range ((e.hom.hom.app X.1).hom ^ b) =
          LinearMap.range ((e.hom.hom.app X.1).hom ^ m) := by
    letI : FiniteDimensional k (M.obj.obj.obj X.1) := M.property.1 X.1
    exact IsArtinian.monotone_stabilizes
      (e.hom.hom.app X.1).hom.iterateRange
  let bound (X : S) : ℕ := (hstabilizes X).choose
  have bound_spec (X : S) : ∀ m, bound X ≤ m →
      LinearMap.range ((e.hom.hom.app X.1).hom ^ bound X) =
        LinearMap.range ((e.hom.hom.app X.1).hom ^ m) :=
    (hstabilizes X).choose_spec
  let n := Finset.univ.sup bound + 1
  refine ⟨n, Nat.zero_lt_succ _, ?_⟩
  intro X
  have hbound : bound X ≤ n :=
    (Finset.le_sup (s := Finset.univ) (f := bound)
      (Finset.mem_univ X)).trans (Nat.le_succ _)
  exact (bound_spec X n hbound).symm.trans
    (bound_spec X (2 * n) (hbound.trans (by omega)))

private theorem exists_isIso_imageRestriction_pow
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (e : M ⟶ M) :
    ∃ n : ℕ, 0 < n ∧ IsIso
      (Abelian.image.ι (endomorphismPower e n) ≫
        Abelian.factorThruImage (endomorphismPower e n)) := by
  classical
  obtain ⟨n, hn, hstable⟩ := exists_uniform_range_pow_stable M e
  refine ⟨n, hn, ?_⟩
  let a : M ⟶ M := endomorphismPower e n
  let Q := Abelian.image a
  let q : M ⟶ Q := Abelian.factorThruImage a
  let i : Q ⟶ M := Abelian.image.ι a
  let t : Q ⟶ Q := i ≫ q
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let I := (IsLinearModule (C := C) k).ι
  letI : J.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsFiniteDimensionalModule (C := C) k)
  letI : I.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsLinearModule (C := C) k)
  letI : J.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (IsFiniteDimensionalModule (C := C) k)
  letI : I.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (IsLinearModule (C := C) k)
  haveI : Mono (I.map (J.map i)) := I.map_mono (J.map i)
  haveI : Epi (I.map (J.map q)) := I.map_epi (J.map q)
  haveI hiApp (X : C) : Mono ((I.map (J.map i)).app X) := inferInstance
  haveI hqApp (X : C) : Epi ((I.map (J.map q)).app X) := inferInstance
  haveI htApp (X : C) : IsIso ((I.map (J.map t)).app X) := by
    change IsIso (t.hom.hom.app X)
    letI : FiniteDimensional k (Q.obj.obj.obj X) := Q.property.1 X
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have hiinj : Function.Injective ((I.map (J.map i)).app X) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    change Function.Injective (i.hom.hom.app X) at hiinj
    have hqsurj : Function.Surjective ((I.map (J.map q)).app X) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    change Function.Surjective (q.hom.hom.app X) at hqsurj
    have hfac := congrArg
      (fun f : M ⟶ M ↦ f.hom.hom.app X) (Abelian.image.fac a)
    have hfacApply (x : M.obj.obj.obj X) :
        i.hom.hom.app X (q.hom.hom.app X x) =
          a.hom.hom.app X x := by
      exact ConcreteCategory.congr_hom hfac x
    have hsurj : Function.Surjective (t.hom.hom.app X) := by
      intro y
      obtain ⟨p, hp⟩ := hqsurj y
      by_cases hPX : Nontrivial (M.obj.obj.obj X)
      · let XS : moduleSupport k M.obj.obj := ⟨X, hPX⟩
        have hrange := hstable XS
        have hmem :
            ((e.hom.hom.app X).hom ^ n) p ∈
              LinearMap.range ((e.hom.hom.app X).hom ^ (2 * n)) := by
          rw [← hrange]
          exact LinearMap.mem_range_self _ p
        obtain ⟨r, hr⟩ := hmem
        refine ⟨q.hom.hom.app X r, ?_⟩
        apply hiinj
        rw [← hp]
        change i.hom.hom.app X
            (q.hom.hom.app X
              (i.hom.hom.app X (q.hom.hom.app X r))) =
          i.hom.hom.app X (q.hom.hom.app X p)
        simp only [hfacApply]
        change a.hom.hom.app X (a.hom.hom.app X r) =
          a.hom.hom.app X p
        simp only [a, endomorphismPower_app_hom]
        change (((e.hom.hom.app X).hom ^ n) *
          ((e.hom.hom.app X).hom ^ n)) r =
            ((e.hom.hom.app X).hom ^ n) p
        rw [← pow_add]
        simpa [two_mul] using hr
      · haveI : Subsingleton (M.obj.obj.obj X) :=
          not_nontrivial_iff_subsingleton.mp hPX
        refine ⟨0, ?_⟩
        apply hiinj
        exact Subsingleton.elim _ _
    exact ⟨
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).2 hsurj,
      hsurj⟩
  haveI : IsIso (I.map (J.map t)) := NatIso.isIso_of_isIso_app _
  haveI : IsIso (J.map t) := isIso_of_reflects_iso (J.map t) I
  haveI : IsIso t := isIso_of_reflects_iso t J
  change IsIso t
  infer_instance

private theorem exists_projective_stableImage_lt
    (P : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (hP : Projective P) (e : P ⟶ P) (hnot : ¬ IsIso e) :
    ∃ n : ℕ, 0 < n ∧
      Projective (Abelian.image (endomorphismPower e n)) ∧
      moduleTotalDimension (Abelian.image (endomorphismPower e n)) <
        moduleTotalDimension P := by
  classical
  obtain ⟨n, hn, hrestricted⟩ :=
    exists_isIso_imageRestriction_pow P e
  let a : P ⟶ P := endomorphismPower e n
  let Q := Abelian.image a
  let q : P ⟶ Q := Abelian.factorThruImage a
  let i : Q ⟶ P := Abelian.image.ι a
  let t : Q ⟶ Q := i ≫ q
  haveI ht : IsIso t := by
    exact hrestricted
  let s : Q ⟶ P := inv t ≫ i
  have hs : s ≫ q = 𝟙 Q := by
    simp [s, t, Category.assoc]
  have hQ : Projective Q := projective_of_retract hP s q hs
  haveI : Projective Q := hQ
  haveI : IsSplitMono s := IsSplitMono.mk'
    { retraction := q, id := hs }
  let d := splitMonoComplement s
  let b : P ≅ Q ⊞ d.complement :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hdim := moduleTotalDimension_biprod b
  have hsnot : ¬ IsIso s := by
    intro hsiso
    letI : IsIso s := hsiso
    haveI : IsIso i := by
      haveI : IsIso (inv t ≫ i) := by
        change IsIso s
        infer_instance
      exact IsIso.of_isIso_comp_left (inv t) i
    haveI : Epi a := by
      rw [← Abelian.image.fac a]
      infer_instance
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hepi : Epi e := by
      apply epi_of_epi_fac (h := endomorphismPower e (m + 1))
      exact (endomorphismPower_succ_right e m).symm
    letI : Epi e := hepi
    exact hnot (isIso_of_epi_finiteDimensionalModule_endo P e)
  have hdnot : ¬ IsZero d.complement := by
    intro hd
    apply hsnot
    apply IsIso.mk
    refine ⟨retraction s, IsSplitMono.id s, ?_⟩
    rw [← d.total]
    have hp : d.projection = 0 := hd.eq_of_tgt _ _
    have hi : d.inclusion = 0 := hd.eq_of_src _ _
    rw [hp, hi, zero_comp, add_zero]
  have hdpos : 0 < moduleTotalDimension d.complement := by
    exact Nat.pos_of_ne_zero fun hz ↦
      hdnot (isZero_of_moduleTotalDimension_eq_zero d.complement hz)
  refine ⟨n, hn, hQ, ?_⟩
  rw [hdim]
  exact Nat.lt_add_of_pos_right hdpos

/-- Enough projectives imply existence of minimal projective presentations
in the finite-support pointwise finite-dimensional module category. -/
theorem minimalProjectivePresentation_nonempty_of_enoughProjectives
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Nonempty (MinimalProjectivePresentation M) := by
  classical
  let Candidate : ℕ → Prop := fun d ↦
    ∃ P : ProjectivePresentation M, moduleTotalDimension P.p = d
  have hCandidate : ∃ d, Candidate d := by
    obtain ⟨P⟩ :=
      (inferInstance : Nonempty (ProjectivePresentation M))
    exact ⟨moduleTotalDimension P.p, P, rfl⟩
  let d := Nat.find hCandidate
  obtain ⟨P, hPdim⟩ := Nat.find_spec hCandidate
  refine ⟨{
    toProjectivePresentation := P
    rightMinimal := ?_ }⟩
  intro e he
  by_contra hnot
  obtain ⟨n, hn, hQprojective, hQlt⟩ :=
    exists_projective_stableImage_lt P.p P.projective e hnot
  let a : P.p ⟶ P.p := endomorphismPower e n
  let Q := Abelian.image a
  let q : P.p ⟶ Q := Abelian.factorThruImage a
  let i : Q ⟶ P.p := Abelian.image.ι a
  let fQ : Q ⟶ M := i ≫ P.f
  have hfQepi : Epi fQ := by
    have hfac : q ≫ fQ = P.f := by
      dsimp only [fQ]
      rw [← Category.assoc, Abelian.image.fac]
      exact endomorphismPower_comp_eq e P.f he n
    exact epi_of_epi_fac hfac
  let QPresentation : ProjectivePresentation M :=
    { p := Q
      projective := hQprojective
      f := fQ
      epi := hfQepi }
  have hminimal : d ≤ moduleTotalDimension Q :=
    Nat.find_min' hCandidate ⟨QPresentation, rfl⟩
  change moduleTotalDimension P.p = d at hPdim
  rw [← hPdim] at hminimal
  exact (Nat.not_lt_of_ge hminimal) hQlt

/-- Finite representables therefore supply minimal projective presentations
for every finite module. -/
theorem finiteDimensionalModule_minimalProjectivePresentation_nonempty
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Nonempty (MinimalProjectivePresentation M) := by
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  exact minimalProjectivePresentation_nonempty_of_enoughProjectives M

/-- Finite representables supply two-step minimal projective presentations
for every finite module. -/
theorem finiteDimensionalModule_twoStepMinimalProjectivePresentation_nonempty
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Nonempty (TwoStepMinimalProjectivePresentation M) := by
  obtain ⟨P₀⟩ :=
    finiteDimensionalModule_minimalProjectivePresentation_nonempty hP M
  obtain ⟨P₁⟩ :=
    finiteDimensionalModule_minimalProjectivePresentation_nonempty hP
      (kernel P₀.f)
  exact ⟨{ augmentation := P₀, syzygyPresentation := P₁ }⟩

end MagnitudeConjecture.CoveringHom
