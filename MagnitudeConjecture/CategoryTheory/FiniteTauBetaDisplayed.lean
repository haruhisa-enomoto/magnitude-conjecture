import MagnitudeConjecture.CategoryTheory.FiniteTauBeta
import MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd

/-! # The beta count from an arbitrary displayed minimal almost-split source -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution QuotientSubmoduleEquidistribution.Iyama
namespace MagnitudeConjecture.FiniteTauMatrix
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteBiproducts C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- Any finite displayed indecomposable source of a minimal right almost-split
map computes the right beta count by its actual nonprojective summands. -/
theorem betaAt_eq_natCard_of_minimalRightAlmostSplit
    (T : FiniteRightTauCategoryData C Ind) (target : Ind)
    (hprojective : ∀ j, T.IsProjective j ↔ Projective (T.obj j))
    {E : C} (f : E ⟶ T.obj target) (hf : IsRightAlmostSplit f) (hmin : IsRightMinimal f)
    (n : ℕ) (V : Fin n → C) (hV : ∀ i, Indecomposable (V i))
    (d : E ≅ ⨁ V) :
    betaAt T target = Nat.card {i : Fin n // ¬ Projective (V i)} := by
  classical
  choose label e using fun i ↦ T.obj_complete (V i) (hV i)
  let ei (i : Fin n) : V i ≅ T.obj (label i) := Classical.choice (e i)
  obtain ⟨em, _⟩ := exists_rightAlmostSplit_middleIso
    (rightMesh_terminal_isRightAlmostSplit T target)
    (rightMesh_terminal_isRightMinimal T target) hf hmin
  have hdecomp : Nonempty ((T.rightMesh (T.obj target)).X₂ ≅ ⨁ fun i ↦ T.obj (label i)) :=
    ⟨em ≪≫ d ≪≫ biproduct.mapIso ei⟩
  rw [betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition T target label hdecomp]
  apply Nat.card_congr
  apply (Equiv.refl (Fin n)).subtypeEquiv
  intro i
  apply not_congr
  exact (hprojective (label i)).trans
    ⟨fun h ↦ Projective.of_iso (ei i).symm h, fun h ↦ Projective.of_iso (ei i) h⟩

/-- The same count for any small finite occurrence index type. -/
theorem betaAt_eq_natCard_of_minimalRightAlmostSplit_fintype
    (T : FiniteRightTauCategoryData C Ind) (target : Ind)
    (hprojective : ∀ j, T.IsProjective j ↔ Projective (T.obj j))
    {E : C} (f : E ⟶ T.obj target) (hf : IsRightAlmostSplit f) (hmin : IsRightMinimal f)
    {ι : Type} [Fintype ι] (V : ι → C) (hV : ∀ i, Indecomposable (V i))
    (d : E ≅ ⨁ V) : betaAt T target = Nat.card {i : ι // ¬ Projective (V i)} := by
  let e := (Fintype.equivFin ι).symm
  have h := betaAt_eq_natCard_of_minimalRightAlmostSplit T target hprojective f hf hmin
    (Fintype.card ι) (V ∘ e) (fun i ↦ hV (e i)) (d ≪≫ (biproduct.reindex e V).symm)
  exact h.trans (Nat.card_congr (e.subtypeEquiv (fun _ ↦ Iff.rfl)))

universe u' v'
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable [HasFiniteBiproducts D] [HasBinaryBiproducts D]

/-- An explicit minimal almost-split source in an equivalent category bounds
its number of nonprojective summands by the target algebra's beta invariant. -/
theorem nonprojective_card_le_beta_of_equivalence
    (T : FiniteRightTauCategoryData C Ind) (E : D ≌ C) [E.functor.Additive]
    (hprojective : ∀ j, T.IsProjective j ↔ Projective (T.obj j))
    {M Y : D} (f : M ⟶ Y) (hf : IsRightAlmostSplit f) (hmin : IsRightMinimal f)
    (hY : Indecomposable Y) (hnY : ¬ Projective Y)
    {ι : Type} [Fintype ι] (V : ι → D) (hV : ∀ i, Indecomposable (V i))
    (d : M ≅ ⨁ V) : Nat.card {i : ι // ¬ Projective (V i)} ≤ beta T := by
  have hEY : Indecomposable (E.functor.obj Y) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence E.functor Y).mpr hY
  obtain ⟨j, ⟨ej⟩⟩ := T.obj_complete (E.functor.obj Y) hEY
  let g := E.functor.map f ≫ ej.hom
  have hg := (hf.map_equivalence E).postcomp_iso ej
  have hgmin := (hmin.map_equivalence E).postcomp_iso ej
  have hd : E.functor.obj M ≅ ⨁ (fun i ↦ E.functor.obj (V i)) :=
    E.functor.mapIso d ≪≫ E.functor.mapBiproduct V
  have hc := betaAt_eq_natCard_of_minimalRightAlmostSplit_fintype T j hprojective g hg hgmin
    (fun i ↦ E.functor.obj (V i))
    (fun i ↦ (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor (V i)).mpr (hV i)) hd
  have hcard : Nat.card {i : ι // ¬ Projective (V i)} =
      Nat.card {i : ι // ¬ Projective (E.functor.obj (V i))} :=
    Nat.card_congr ((Equiv.refl ι).subtypeEquiv
      (fun i ↦ not_congr (E.map_projective_iff (V i)).symm))
  rw [hcard, ← hc]
  apply (beta_le_iff T (beta T)).mp le_rfl j
  intro hp
  have hpj : Projective (T.obj j) := (hprojective j).mp hp
  exact hnY ((E.map_projective_iff Y).mp
    (Projective.of_iso ej.symm hpj))

end MagnitudeConjecture.FiniteTauMatrix
