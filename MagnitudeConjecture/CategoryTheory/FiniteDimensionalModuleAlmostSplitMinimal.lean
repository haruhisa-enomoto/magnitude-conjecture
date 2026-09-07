import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.AlmostSplitShortExact
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite

/-!
# Minimalizing almost-split maps of finite modules

Any right almost-split map between finite-support pointwise
finite-dimensional modules can be replaced by a right-minimal one.  The
proof minimizes total pointwise dimension of the source.  A noninvertible
endomorphism fixing a minimal candidate would make its categorical image a
strictly smaller right almost-split source.

The exact dual construction minimizes the target of a left almost-split
morphism.
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

/-- A right almost-split morphism with finite-dimensional source can be
replaced by a right-minimal right almost-split morphism to the same target. -/
theorem finiteDimensionalModule_exists_rightMinimal_rightAlmostSplit
    {M E : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (f : E ⟶ M) (hf : IsRightAlmostSplit f) :
    ∃ (E' : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
      (f' : E' ⟶ M), IsRightAlmostSplit f' ∧ IsRightMinimal f' := by
  classical
  let Candidate : ℕ → Prop := fun d ↦
    ∃ (E' : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
      (f' : E' ⟶ M), IsRightAlmostSplit f' ∧
        moduleTotalDimension E' = d
  have hCandidate : ∃ d, Candidate d :=
    ⟨moduleTotalDimension E, E, f, hf, rfl⟩
  let d := Nat.find hCandidate
  obtain ⟨Emin, fmin, hfmin, hdim⟩ := Nat.find_spec hCandidate
  have hminimal : IsRightMinimal fmin := by
    intro e he
    by_contra hnot
    let I := Abelian.image e
    let i : I ⟶ Emin := Abelian.image.ι e
    let q : Emin ⟶ I := Abelian.factorThruImage e
    let fI : I ⟶ M := i ≫ fmin
    have hfI : IsRightAlmostSplit fI := by
      constructor
      · intro hsplit
        obtain ⟨s⟩ := hsplit.exists_splitEpi
        apply hfmin.not_isSplitEpi
        exact IsSplitEpi.mk'
          { section_ := s.section_ ≫ i
            id := by simpa only [fI, Category.assoc] using s.id }
      · intro X g hg
        obtain ⟨h, hh⟩ := hfmin.factors g hg
        refine ⟨h ≫ q, ?_⟩
        calc
          (h ≫ q) ≫ fI = h ≫ (q ≫ i) ≫ fmin := by
            simp only [fI, Category.assoc]
          _ = h ≫ e ≫ fmin := by rw [Abelian.image.fac]
          _ = h ≫ fmin := by rw [he]
          _ = g := hh
    have hsmaller : moduleTotalDimension I < moduleTotalDimension Emin :=
      moduleTotalDimension_image_lt_of_not_isIso Emin e hnot
    have hnew : Candidate (moduleTotalDimension I) :=
      ⟨I, fI, hfI, rfl⟩
    have hleast : d ≤ moduleTotalDimension I :=
      Nat.find_min' hCandidate hnew
    rw [hdim] at hsmaller
    exact (Nat.not_lt_of_ge hleast) hsmaller
  exact ⟨Emin, fmin, hfmin, hminimal⟩

/-- A left almost-split morphism with finite-dimensional target can be
replaced by a left-minimal left almost-split morphism from the same source. -/
theorem finiteDimensionalModule_exists_leftMinimal_leftAlmostSplit
    {M E : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (f : M ⟶ E) (hf : IsLeftAlmostSplit f) :
    ∃ (E' : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
      (f' : M ⟶ E'), IsLeftAlmostSplit f' ∧ IsLeftMinimal f' := by
  classical
  let Candidate : ℕ → Prop := fun d ↦
    ∃ (E' : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
      (f' : M ⟶ E'), IsLeftAlmostSplit f' ∧
        moduleTotalDimension E' = d
  have hCandidate : ∃ d, Candidate d :=
    ⟨moduleTotalDimension E, E, f, hf, rfl⟩
  let d := Nat.find hCandidate
  obtain ⟨Emin, fmin, hfmin, hdim⟩ := Nat.find_spec hCandidate
  have hminimal : IsLeftMinimal fmin := by
    intro e he
    by_contra hnot
    let I := Abelian.image e
    let q : Emin ⟶ I := Abelian.factorThruImage e
    let fI : M ⟶ I := fmin ≫ q
    have hfI : IsLeftAlmostSplit fI := by
      exact MagnitudeConjecture.CategoryTheory.IsLeftAlmostSplit.comp_factorThruImage_of_comp_eq_self
        fmin hfmin e he
    have hsmaller : moduleTotalDimension I < moduleTotalDimension Emin :=
      moduleTotalDimension_image_lt_of_not_isIso Emin e hnot
    have hnew : Candidate (moduleTotalDimension I) :=
      ⟨I, fI, hfI, rfl⟩
    have hleast : d ≤ moduleTotalDimension I :=
      Nat.find_min' hCandidate hnew
    rw [hdim] at hsmaller
    exact (Nat.not_lt_of_ge hleast) hsmaller
  exact ⟨Emin, fmin, hfmin, hminimal⟩

end MagnitudeConjecture.CoveringHom
