import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverArrowRepresentatives
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedOccurrenceBasis

/-!
# Fullness for arbitrary ordinary-arrow representatives

Any representatives of the ordinary arrows span the first layer of the radical filtration.  Their
composites then span every successive layer modulo the next one, and
nilpotence terminates the approximation.  Over an algebraically closed field,
an endomorphism of an indecomposable projective is a scalar identity modulo
the radical, so every representative-dependent free path realization is full.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

local instance fullnessRestrictedModule (i : Fin S.n) :
    Module k (S.almostSplitSkeleton.obj i) :=
  Module.restrictScalars k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i)

local instance fullnessRestrictedScalarTower (i : Fin S.n) :
    IsScalarTower k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i) :=
  IsScalarTower.restrictScalars k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i)

namespace OrdinaryArrowRepresentatives

/-- The realized linear combinations of ordinary paths from `x` to `y`. -/
def pathImage (D : S.OrdinaryArrowRepresentatives) (x y : S.ProjectiveLabel) :
    Submodule k (S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) :=
  Submodule.span k (Set.range fun p : Quiver.Path x y ↦ D.pathMap p)

theorem hom_mem_pathImage (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    D.hom a ∈ D.pathImage x y := by
  apply Submodule.subset_span
  refine ⟨(show Quiver.Path x y from (show x ⟶ y from a).toPath), ?_⟩
  change D.pathMap
      (show Quiver.Path x y from (show x ⟶ y from a).toPath) = _
  rw [show (show x ⟶ y from a).toPath = Quiver.Path.nil.cons a by rfl,
    pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil,
    Category.comp_id]

theorem identity_mem_pathImage (D : S.OrdinaryArrowRepresentatives)
    (x : S.ProjectiveLabel) :
    𝟙 (S.ordinaryProjectiveObj x) ∈ D.pathImage x x := by
  apply Submodule.subset_span
  exact ⟨Quiver.Path.nil, LinearPathCategory.pathMap_nil _ _ _⟩

/-- Realized path combinations are closed under composition. -/
theorem pathImage_comp (D : S.OrdinaryArrowRepresentatives)
    {x y z : S.ProjectiveLabel}
    {f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj z}
    {g : S.ordinaryProjectiveObj z ⟶ S.ordinaryProjectiveObj x}
    (hf : f ∈ D.pathImage z y)
    (hg : g ∈ D.pathImage x z) :
    f ≫ g ∈ D.pathImage x y := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨q, rfl⟩ := hg
          apply Submodule.subset_span
          exact ⟨q.comp p,
            (LinearPathCategory.pathMap_comp
              S.ordinaryProjectiveObj
              (fun {_ _} (a : S.OrdinaryArrow _ _) ↦
                D.hom a) q p)⟩
      | zero => simp
      | add g h _ _ hg hh => simpa using Submodule.add_mem _ hg hh
      | smul c g _ hg => simpa using Submodule.smul_mem _ c hg
  | zero => simp
  | add f h _ _ hf hh => simpa using Submodule.add_mem _ hf hh
  | smul c f _ hf => simpa using Submodule.smul_mem _ c hf

/-- A radical morphism is a realized linear combination of arrows modulo
the square of the projective radical. -/
theorem exists_pathImage_radical_approximation
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel}
    {f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x}
    (hf : f ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x)) :
    ∃ g : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x,
      g ∈ D.pathImage x y ∧
      g ∈ S.projectiveNilpotentRadicalData.ideal.hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) ∧
      f - g ∈ (S.projectiveNilpotentRadicalData.ideal.pow 2).hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) := by
  classical
  let Rad := S.projectiveRadicalSubmodule x y
  let SqInRad := S.projectiveRadicalSquareInRadicalSubmodule x y
  let fRad : Rad := ⟨f, hf⟩
  let c := (S.ordinaryArrowBasis x y).repr (SqInRad.mkQ fRad)
  let gRad : Rad := ∑ a, c a • D.representative a
  let g : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x := gRad.1
  have hgEq : g = ∑ a, c a • D.hom a := by
    dsimp only [g, gRad]
    exact map_sum Rad.subtype
      (fun a ↦ c a • D.representative a) Finset.univ
  have hgPath : g ∈ D.pathImage x y := by
    rw [hgEq]
    exact Submodule.sum_mem _ fun a _ ↦
      Submodule.smul_mem _ _ (D.hom_mem_pathImage a)
  have hgRad : g ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) := gRad.2
  have hquot : SqInRad.mkQ gRad = SqInRad.mkQ fRad := by
    calc
      SqInRad.mkQ gRad =
          ∑ a, c a • S.ordinaryArrowClass a := by
        dsimp only [gRad]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [map_smul]
        exact congrArg (fun z ↦ c a • z)
          (D.representative_mkQ a)
      _ = SqInRad.mkQ fRad := by
        exact (S.ordinaryArrowBasis x y).sum_repr (SqInRad.mkQ fRad)
  have hdiff : f - g ∈ S.projectiveRadicalSquareSubmodule x y := by
    have hsub : fRad.1 - gRad.1 ∈
        S.projectiveRadicalSquareSubmodule x y := by
      exact (Submodule.Quotient.eq SqInRad).1 hquot.symm
    exact hsub
  exact ⟨g, hgPath, hgRad, hdiff⟩

/-- Every positive projective-radical layer is represented by realized paths
modulo the next layer.  The representative remains in the original layer. -/
theorem exists_pathImage_radicalPower_approximation :
    ∀ (D : S.OrdinaryArrowRepresentatives) (n : ℕ)
      {x y : S.ProjectiveLabel}
      {f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x},
      f ∈ (S.projectiveNilpotentRadicalData.ideal.pow (n + 1)).hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) →
      ∃ g : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x,
        g ∈ D.pathImage x y ∧
        g ∈ (S.projectiveNilpotentRadicalData.ideal.pow (n + 1)).hom
          (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) ∧
        f - g ∈ (S.projectiveNilpotentRadicalData.ideal.pow (n + 2)).hom
          (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) := by
  intro D n
  induction n with
  | zero =>
      intro x y f hf
      have hf' : f ∈ S.projectiveNilpotentRadicalData.ideal.hom
          (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) := by
        simpa only [zero_add, HomIdeal.pow_one] using hf
      obtain ⟨g, hgPath, hgRad, hrem⟩ :=
        D.exists_pathImage_radical_approximation hf'
      refine ⟨g, hgPath, ?_, ?_⟩
      · simpa only [zero_add, HomIdeal.pow_one] using hgRad
      · simpa only [zero_add] using hrem
  | succ n ih =>
      intro x y f hf
      have hf' : f ∈
          (S.projectiveNilpotentRadicalData.ideal.pow (n + 1) ⋆ᵢ
            S.projectiveNilpotentRadicalData.ideal).hom
            (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
          HomIdeal.pow_succ] using hf
      refine AddSubgroup.closure_induction
        (p := fun f _ ↦
          ∃ g : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x,
            g ∈ D.pathImage x y ∧
            g ∈ (S.projectiveNilpotentRadicalData.ideal.pow
                (Nat.succ n + 1)).hom
              (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) ∧
            f - g ∈ (S.projectiveNilpotentRadicalData.ideal.pow
                (Nat.succ n + 2)).hom
              (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x))
        ?_ ?_ ?_ ?_ hf'
      · intro f hfgen
        obtain ⟨z, a, b, ha, hb, rfl⟩ := hfgen
        change S.ProjectiveLabel at z
        change S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj z at a
        change S.ordinaryProjectiveObj z ⟶ S.ordinaryProjectiveObj x at b
        obtain ⟨a₀, ha₀Path, ha₀Pow, haRem⟩ :=
          ih (x := z) (y := y) ha
        obtain ⟨b₀, hb₀Path, hb₀Rad, hbRem⟩ :=
          D.exists_pathImage_radical_approximation
            (x := x) (y := z) hb
        let g := a₀ ≫ b₀
        have hgPath : g ∈ D.pathImage x y :=
          D.pathImage_comp ha₀Path hb₀Path
        have hgPow : g ∈
            (S.projectiveNilpotentRadicalData.ideal.pow (n + 2)).hom
              (S.ordinaryProjectiveObj y)
              (S.ordinaryProjectiveObj x) := by
          change a₀ ≫ b₀ ∈ _
          simpa only [show n + 2 = (n + 1) + 1 by omega,
            HomIdeal.pow_succ] using HomIdeal.comp_mem_mul ha₀Pow hb₀Rad
        have hleft : (a - a₀) ≫ b₀ ∈
            (S.projectiveNilpotentRadicalData.ideal.pow (n + 3)).hom
              (S.ordinaryProjectiveObj y)
              (S.ordinaryProjectiveObj x) := by
          simpa only [show n + 3 = (n + 2) + 1 by omega,
            HomIdeal.pow_succ] using HomIdeal.comp_mem_mul haRem hb₀Rad
        have hright : a ≫ (b - b₀) ∈
            (S.projectiveNilpotentRadicalData.ideal.pow (n + 3)).hom
              (S.ordinaryProjectiveObj y)
              (S.ordinaryProjectiveObj x) := by
          have hmul := HomIdeal.comp_mem_mul ha hbRem
          rw [← HomIdeal.pow_add] at hmul
          simpa only [show (n + 1) + 2 = n + 3 by omega] using hmul
        refine ⟨g, hgPath, ?_, ?_⟩
        · simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hgPow
        · have hadd := AddSubgroup.add_mem _ hleft hright
          have heq : a ≫ b - g = (a - a₀) ≫ b₀ + a ≫ (b - b₀) := by
            dsimp only [g]
            simp only [Preadditive.sub_comp, Preadditive.comp_sub]
            abel
          rw [heq]
          simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hadd
      · exact ⟨0, Submodule.zero_mem _, by simp, by simp⟩
      · intro f h _ _ hf hh
        obtain ⟨f₀, hf₀Path, hf₀Pow, hfRem⟩ := hf
        obtain ⟨h₀, hh₀Path, hh₀Pow, hhRem⟩ := hh
        refine ⟨f₀ + h₀, Submodule.add_mem _ hf₀Path hh₀Path,
          AddSubgroup.add_mem _ hf₀Pow hh₀Pow, ?_⟩
        have hadd := AddSubgroup.add_mem _ hfRem hhRem
        convert hadd using 1
        all_goals abel
      · intro f _ hf
        obtain ⟨f₀, hf₀Path, hf₀Pow, hfRem⟩ := hf
        refine ⟨-f₀, Submodule.neg_mem _ hf₀Path,
          AddSubgroup.neg_mem _ hf₀Pow, ?_⟩
        have hneg := AddSubgroup.neg_mem _ hfRem
        convert hneg using 1
        all_goals abel

/-- If a later radical layer vanishes, every morphism in a positive earlier
layer is already a realized linear combination of paths. -/
theorem radicalPower_mem_pathImage_of_pow_add_eq_bot :
    ∀ (D : S.OrdinaryArrowRepresentatives) (r n : ℕ)
      {x y : S.ProjectiveLabel}
      {f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x},
      1 ≤ n →
      S.projectiveNilpotentRadicalData.ideal.pow (n + r) = ⊥ →
      f ∈ (S.projectiveNilpotentRadicalData.ideal.pow n).hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) →
      f ∈ D.pathImage x y := by
  intro D r
  induction r with
  | zero =>
      intro n x y f _ hzero hf
      rw [Nat.add_zero] at hzero
      have hfZero : f = 0 := by
        rw [hzero] at hf
        simpa using hf
      subst f
      exact Submodule.zero_mem _
  | succ r ih =>
      intro n x y f hn hzero hf
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      obtain ⟨g, hgPath, _, hrem⟩ :=
        D.exists_pathImage_radicalPower_approximation m hf
      have hzero' : S.projectiveNilpotentRadicalData.ideal.pow
          ((m + 1 + 1) + r) = ⊥ := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hzero
      have hremPath : f - g ∈ D.pathImage x y :=
        ih (n := m + 1 + 1) (by omega) hzero' hrem
      have hadd := Submodule.add_mem _ hgPath hremPath
      convert hadd using 1
      all_goals abel

/-- Every projective-radical morphism is a realized linear combination of
ordinary paths. -/
theorem projectiveRadical_le_ordinaryPathImage
    (D : S.OrdinaryArrowRepresentatives) (x y : S.ProjectiveLabel) :
    HomIdeal.homSubmodule S.projectiveNilpotentRadicalData.ideal
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) ≤
      D.pathImage x y := by
  obtain ⟨N, hN⟩ := S.projectiveNilpotentRadicalData.nilpotent
  intro f hf
  have hzero : S.projectiveNilpotentRadicalData.ideal.pow (1 + N) = ⊥ := by
    rw [Nat.add_comm, HomIdeal.pow_succ, hN]
    simp
  change f ∈ S.projectiveNilpotentRadicalData.ideal.hom
    (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) at hf
  exact D.radicalPower_mem_pathImage_of_pow_add_eq_bot N 1 (by omega)
    hzero (by simpa only [HomIdeal.pow_one] using hf)

end OrdinaryArrowRepresentatives

/-- A morphism between differently labelled selected projectives belongs to
the projective radical. -/
theorem mem_projectiveRadical_of_ne
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    {x y : S.ProjectiveLabel} (hxy : x ≠ y)
    (f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) :
    f ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) := by
  change f ∈ S.projectiveRadicalIdeal.hom
    (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x)
  rw [S.mem_projectiveRadicalIdeal_iff,
    S.fgNilpotentRadicalData.mem_ideal_iff]
  letI : IsLocalRing (End (S.fgObj x.label)) :=
    S.fgObj_end_isLocalRing x.label
  apply (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
    (S.fgObj_indecomposable x.label).1 _).2
  intro hsplit
  letI : IsSplitEpi (S.projectiveInclusion.map f) := hsplit
  letI : IsSplitMono (S.projectiveInclusion.map f) :=
    S.almostSplitSkeleton.isSplitMono_of_isSplitEpi_between_obj
      (S.projectiveInclusion.map f)
  haveI : IsIso (S.projectiveInclusion.map f) :=
    isIso_of_mono_of_isSplitEpi (S.projectiveInclusion.map f)
  apply hxy
  have hlabel : y.label = x.label :=
    S.fgObj_skeletal ⟨asIso (S.projectiveInclusion.map f)⟩
  cases x with
  | mk xl xp =>
      cases y with
      | mk yl yp =>
          simp only at hlabel ⊢
          subst yl
          rfl

variable [IsAlgClosed k]

/-- An endomorphism of a selected indecomposable projective is a scalar
identity modulo the projective radical. -/
theorem exists_scalar_sub_mem_projectiveRadical
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (x : S.ProjectiveLabel)
    (f : S.ordinaryProjectiveObj x ⟶ S.ordinaryProjectiveObj x) :
    ∃ a : k, f - a • 𝟙 (S.ordinaryProjectiveObj x) ∈
      S.projectiveNilpotentRadicalData.ideal.hom
        (S.ordinaryProjectiveObj x) (S.ordinaryProjectiveObj x) := by
  let F : S.fgObj x.label ⟶ S.fgObj x.label :=
    S.projectiveInclusion.map f
  obtain ⟨a, ha⟩ :=
    S.almostSplitSkeleton.exists_scalar_sub_isRadicalMorphism
      (K := k) x.label F
  change CategoricalRadical.IsRadicalMorphism
    (F - a • 𝟙 (S.fgObj x.label)) at ha
  refine ⟨a, ?_⟩
  change f - a • 𝟙 (S.ordinaryProjectiveObj x) ∈
    S.projectiveRadicalIdeal.hom
      (S.ordinaryProjectiveObj x) (S.ordinaryProjectiveObj x)
  rw [S.mem_projectiveRadicalIdeal_iff,
    S.fgNilpotentRadicalData.mem_ideal_iff]
  change CategoricalRadical.IsRadicalMorphism
    (F - a • 𝟙 (S.fgObj x.label))
  exact ha

namespace OrdinaryArrowRepresentatives

/-- Paths realized by any representative system span every morphism between selected
indecomposable projectives. -/
theorem pathImage_eq_top (D : S.OrdinaryArrowRepresentatives)
    (x y : S.ProjectiveLabel) :
    D.pathImage x y = ⊤ := by
  apply top_unique
  intro f _
  by_cases hxy : x = y
  · subst y
    obtain ⟨a, hrad⟩ := S.exists_scalar_sub_mem_projectiveRadical x f
    have hscalar : a • 𝟙 (S.ordinaryProjectiveObj x) ∈
        D.pathImage x x :=
      Submodule.smul_mem _ a (D.identity_mem_pathImage x)
    have hrem : f - a • 𝟙 (S.ordinaryProjectiveObj x) ∈
        D.pathImage x x :=
      D.projectiveRadical_le_ordinaryPathImage x x hrad
    have hadd := Submodule.add_mem _ hscalar hrem
    convert hadd using 1
    all_goals abel
  · exact D.projectiveRadical_le_ordinaryPathImage x y
      (S.mem_projectiveRadical_of_ne hxy f)

/-- Every morphism between selected projectives has a preimage in the free
linear path category under any representative realization. -/
theorem exists_realization_preimage (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) :
    ∃ q : LinearPathCategory.obj k S.ProjectiveLabel y ⟶
        LinearPathCategory.obj k S.ProjectiveLabel x,
      D.realization.map q = f := by
  have hf : f ∈ D.pathImage x y := by
    rw [D.pathImage_eq_top x y]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, rfl⟩ := hf
      refine ⟨LinearPathCategory.pathHom p, ?_⟩
      exact D.realization_map_pathHom p
  | zero => exact ⟨0, by simp⟩
  | add f g _ _ hf hg =>
      obtain ⟨qf, hqf⟩ := hf
      obtain ⟨qg, hqg⟩ := hg
      refine ⟨qf + qg, ?_⟩
      rw [D.realization.map_add, hqf, hqg]
  | smul c f _ hf =>
      obtain ⟨q, hq⟩ := hf
      refine ⟨c • q, ?_⟩
      rw [Functor.map_smul, hq]

/-- Every free linear ordinary-quiver realization is full. -/
noncomputable instance realization_full (D : S.OrdinaryArrowRepresentatives) :
    D.realization.Full where
  map_surjective := by
    intro X Y f
    exact D.exists_realization_preimage
      (x := LinearPathCategory.vertex Y)
      (y := LinearPathCategory.vertex X) f

end OrdinaryArrowRepresentatives

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
