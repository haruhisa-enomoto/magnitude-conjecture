import MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteTauBeta
import MagnitudeConjecture.CategoryTheory.FiniteTauLocalDensity
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd

/-!
# Auslander--Reiten surplus under equivalence

An additive equivalence between abelian categories preserves the total
Auslander--Reiten surplus of two finite right-tau presentations when their
indecomposable labels and represented objects are matched.  This is the
category-independent transport lemma needed to compare finite category
modules with finitely generated modules over a category algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.FiniteTauMatrix

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable [HasFiniteBiproducts D] [HasBinaryBiproducts D]
  [IsIdempotentComplete D]
variable {I : Type w₁} [Fintype I]
variable {J : Type w₂} [Fintype J]

variable
    (T : QuotientSubmoduleEquidistribution.Iyama.FiniteRightTauCategoryData C I)
variable
    (U : QuotientSubmoduleEquidistribution.Iyama.FiniteRightTauCategoryData D J)
variable (E : C ≌ D) [E.functor.Additive]
variable (labelEquiv : I ≃ J)
variable (objIso : ∀ i : I, E.functor.obj (T.obj i) ≅ U.obj (labelEquiv i))

include E objIso in
/-- Incoming right-mesh arity is preserved by an additive equivalence after
matching the indecomposable endpoint labels. -/
theorem rightMiddleArity_eq_of_equivalence (i : I) :
    rightMiddleArity T i = rightMiddleArity U (labelEquiv i) := by
  let d := rightMiddleFiniteIndecomposableDecomposition T i
  let dMap := d.mapOfIndecomposable E.functor fun j ↦
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor (d.summand j)).2 (d.indecomposable j)
  let m := (T.rightMesh (T.obj i)).g ≫ (T.rightTermIso (T.obj i)).hom
  have hmAS : IsRightAlmostSplit m :=
    rightMesh_terminal_isRightAlmostSplit T i
  have hmMin : IsRightMinimal m :=
    rightMesh_terminal_isRightMinimal T i
  have hmapAS :
      IsRightAlmostSplit (E.functor.map m ≫ (objIso i).hom) :=
    (hmAS.map_equivalence E).postcomp_iso (objIso i)
  have hmapMin :
      IsRightMinimal (E.functor.map m ≫ (objIso i).hom) :=
    (hmMin.map_equivalence E).postcomp_iso (objIso i)
  exact (rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
    U (labelEquiv i) dMap hmapAS hmapMin).symm

variable [EnoughProjectives C] [EnoughProjectives D]

omit [E.functor.Additive] in
include E objIso in
/-- The finite-right-tau projectivity predicate is preserved at matched
indecomposable labels. -/
theorem isProjective_equivalence_iff (i : I) :
    T.IsProjective i ↔ U.IsProjective (labelEquiv i) := by
  rw [isProjective_iff_projective_obj,
    isProjective_iff_projective_obj]
  constructor
  · intro h
    exact Projective.of_iso (objIso i)
      ((E.map_projective_iff (T.obj i)).2 h)
  · intro h
    apply (E.map_projective_iff (T.obj i)).1
    exact Projective.of_iso (objIso i).symm h

include E objIso in
/-- The number of nonprojective occurrences in a right almost-split middle
term is preserved at matched labels. -/
theorem betaAt_eq_of_equivalence (i : I) :
    betaAt T i = betaAt U (labelEquiv i) := by
  classical
  let d := rightMiddleFiniteIndecomposableDecomposition T i
  let dMap := d.mapOfIndecomposable E.functor fun j ↦
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor (d.summand j)).2 (d.indecomposable j)
  let m := (T.rightMesh (T.obj i)).g ≫ (T.rightTermIso (T.obj i)).hom
  let u := (U.rightMesh (U.obj (labelEquiv i))).g ≫
    (U.rightTermIso (U.obj (labelEquiv i))).hom
  have hmAS : IsRightAlmostSplit m :=
    rightMesh_terminal_isRightAlmostSplit T i
  have hmMin : IsRightMinimal m :=
    rightMesh_terminal_isRightMinimal T i
  have hmapAS : IsRightAlmostSplit (E.functor.map m ≫ (objIso i).hom) :=
    (hmAS.map_equivalence E).postcomp_iso (objIso i)
  have hmapMin : IsRightMinimal (E.functor.map m ≫ (objIso i).hom) :=
    (hmMin.map_equivalence E).postcomp_iso (objIso i)
  have huAS : IsRightAlmostSplit u :=
    rightMesh_terminal_isRightAlmostSplit U (labelEquiv i)
  have huMin : IsRightMinimal u :=
    rightMesh_terminal_isRightMinimal U (labelEquiv i)
  obtain ⟨middleIso, _⟩ :=
    exists_rightAlmostSplit_middleIso hmapAS hmapMin huAS huMin
  let summandIso : ∀ j : Fin d.n,
      dMap.summand j ≅
        U.obj (labelEquiv (rightMiddleLabel T i j)) := fun j ↦ by
    change E.functor.obj (T.obj (rightMiddleLabel T i j)) ≅ _
    exact objIso (rightMiddleLabel T i j)
  letI : HasBiproductsOfShape (Fin d.n) D :=
    HasFiniteBiproducts.out d.n
  letI : HasBiproduct (fun j : Fin d.n ↦
      U.obj (labelEquiv (rightMiddleLabel T i j))) :=
    HasBiproductsOfShape.has_biproduct _
  have hdecomposition : Nonempty
      ((U.rightMesh (U.obj (labelEquiv i))).X₂ ≅
        ⨁ fun j : Fin d.n ↦
          U.obj (labelEquiv (rightMiddleLabel T i j))) := ⟨
    middleIso.symm ≪≫ dMap.isoBiproduct ≪≫
      biproduct.mapIso
        (f := fun j : Fin d.n ↦ dMap.summand j)
        (g := fun j : Fin d.n ↦
          U.obj (labelEquiv (rightMiddleLabel T i j))) summandIso⟩
  rw [betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition
      T i (rightMiddleLabel T i) (rightMiddleIso T i),
    betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition
      U (labelEquiv i)
        (fun j ↦ labelEquiv (rightMiddleLabel T i j)) hdecomposition]
  exact Nat.card_congr <|
    (Equiv.refl (Fin d.n)).subtypeEquiv fun j ↦
      not_congr (isProjective_equivalence_iff
        T U E labelEquiv objIso (rightMiddleLabel T i j))

include E objIso in
/-- A uniform bound on the nonprojective right-middle multiplicity is
transported by an additive equivalence. -/
theorem beta_le_of_equivalence {bound : ℕ} (h : beta T ≤ bound) :
    beta U ≤ bound := by
  rw [beta_le_iff]
  intro j hj
  let i := labelEquiv.symm j
  have hi : ¬ T.IsProjective i := by
    intro hprojective
    exact hj <| by
      simpa [i] using
        (isProjective_equivalence_iff T U E labelEquiv objIso i).1 hprojective
  have hibound := (beta_le_iff T bound).1 h i hi
  have hbeta := betaAt_eq_of_equivalence T U E labelEquiv objIso i
  simpa [i] using hbeta.symm.trans_le hibound

include E objIso in
/-- A uniform `beta` bound is invariant under an additive equivalence with a
bijective matching of indecomposable labels. -/
theorem beta_le_iff_of_equivalence {bound : ℕ} :
    beta T ≤ bound ↔ beta U ≤ bound := by
  constructor
  · exact beta_le_of_equivalence T U E labelEquiv objIso
  · intro hU
    rw [beta_le_iff]
    intro i hi
    have hUi : ¬ U.IsProjective (labelEquiv i) := by
      intro hprojective
      exact hi <|
        (isProjective_equivalence_iff T U E labelEquiv objIso i).2
          hprojective
    have hbound := (beta_le_iff U bound).1 hU (labelEquiv i) hUi
    exact (betaAt_eq_of_equivalence T U E labelEquiv objIso i).trans_le
      hbound

include E objIso in
/-- Matrix local density is preserved at every matched label. -/
theorem localDensity_eq_of_equivalence (i : I) :
    @ARCount.localDensity I inferInstance (arrowMultiplicity T)
        T.IsProjective (Classical.decPred _) i =
      @ARCount.localDensity J inferInstance (arrowMultiplicity U)
        U.IsProjective (Classical.decPred _) (labelEquiv i) := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity T i
      (rightMiddleArity T i) rfl (T.IsProjective i) Iff.rfl,
    localDensity_eq_localDensityOfIncomingArity U (labelEquiv i)
      (rightMiddleArity T i)
      (rightMiddleArity_eq_of_equivalence T U E labelEquiv objIso i).symm
      (T.IsProjective i)
      (isProjective_equivalence_iff T U E labelEquiv objIso i).symm]

include E labelEquiv objIso in
/-- Matched finite right-tau presentations in equivalent abelian categories
have the same Auslander--Reiten surplus. -/
theorem surplus_eq_of_equivalence :
    @ARCount.surplus I inferInstance (arrowMultiplicity T)
        T.IsProjective (Classical.decPred _) =
      @ARCount.surplus J inferInstance (arrowMultiplicity U)
        U.IsProjective (Classical.decPred _) := by
  classical
  rw [← ARCount.sum_localDensity_eq_surplus,
    ← ARCount.sum_localDensity_eq_surplus]
  exact Fintype.sum_bijective labelEquiv labelEquiv.bijective
    (fun i ↦ ARCount.localDensity (arrowMultiplicity T) T.IsProjective i)
    (fun j ↦ ARCount.localDensity (arrowMultiplicity U) U.IsProjective j)
    (localDensity_eq_of_equivalence T U E labelEquiv objIso)

end MagnitudeConjecture.FiniteTauMatrix
