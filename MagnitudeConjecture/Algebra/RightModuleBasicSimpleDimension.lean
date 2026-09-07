import MagnitudeConjecture.Algebra.RightModulePrimitiveProjectiveCount
import MagnitudeConjecture.Algebra.BiserialSemisimpleSubmodule
import MagnitudeConjecture.Algebra.BiserialCokernelObstruction
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedOccurrenceBasis

/-!
# Simple dimensions for a complete primitive-projective presentation

A complete orthogonal family decomposes every right module into its
idempotent coordinates.  When the family contains exactly one primitive
projective from each selected isomorphism class, algebraic closedness makes
every simple right module one-dimensional.  Consequently a semisimple module
of composition length at most two has ground-field dimension at most two.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (X : FinitelyGeneratedCategory A)
variable {I : Type*} [Fintype I]

local instance : Module k X :=
  Module.restrictScalars k Aᵐᵒᵖ X

local instance : IsScalarTower k Aᵐᵒᵖ X :=
  IsScalarTower.restrictScalars k Aᵐᵒᵖ X

local instance : Module.Finite k X :=
  finite_over_field_of_finitelyGenerated k A X

/-- A complete orthogonal idempotent family decomposes a right module into
the product of its idempotent coordinates. -/
def completeIdempotentCoordinateEquiv
    (e : I → A) (hall : CompleteOrthogonalIdempotents e) :
    X ≃ₗ[k] (∀ i, idempotentCoordinate (k := k) (e i) X) where
  toFun x i := ⟨(MulOpposite.op (e i)) • x, ⟨x, rfl⟩⟩
  invFun x := ∑ i, (x i).1
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' r x := by
    funext i
    apply Subtype.ext
    exact smul_comm (MulOpposite.op (e i)) r x
  left_inv x := by
    change (∑ i, (MulOpposite.op (e i)) • x) = x
    rw [← Finset.sum_smul]
    have hop : ∑ i, MulOpposite.op (e i) =
        MulOpposite.op (∑ i, e i) := by simp
    rw [hop, hall.complete]
    simp
  right_inv x := by
    funext j
    apply Subtype.ext
    change (MulOpposite.op (e j)) • (∑ i, (x i).1) = (x j).1
    rw [Finset.smul_sum]
    classical
    rw [Finset.sum_eq_single j]
    · exact idempotentCoordinate_fixed (hall.idem j) X (x j)
    · intro i _ hij
      rw [← idempotentCoordinate_fixed (hall.idem i) X (x i),
        ← mul_smul]
      change (MulOpposite.op (e i * e j)) • (x i).1 = 0
      rw [hall.ortho hij, MulOpposite.op_zero, zero_smul]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim

/-- Ground-field dimension is the sum of the dimensions of all coordinates
of a complete orthogonal idempotent family. -/
theorem finrank_eq_sum_finrank_idempotentCoordinate
    (e : I → A) (hall : CompleteOrthogonalIdempotents e) :
    Module.finrank k X =
      ∑ i, Module.finrank k (idempotentCoordinate (k := k) (e i) X) := by
  rw [(completeIdempotentCoordinateEquiv (k := k) X e hall).finrank_eq,
    Module.finrank_pi_fintype]

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance fgRestrictedModule
    (X : RightModule.FinitelyGeneratedCategory A) : Module k X :=
  Module.restrictScalars k Aᵐᵒᵖ X

local instance fgRestrictedScalarTower
    (X : RightModule.FinitelyGeneratedCategory A) :
    IsScalarTower k Aᵐᵒᵖ X :=
  IsScalarTower.restrictScalars k Aᵐᵒᵖ X

/-- The Hom space from an indecomposable projective to its simple top is
one-dimensional over an algebraically closed field. -/
theorem finrank_hom_projectiveSimpleTop_self_eq_one_of_isAlgClosed
    (p : S.ProjectiveLabel) :
    Module.finrank k
      (S.fgObj p.label ⟶ S.projectiveSimpleTop p) = 1 := by
  letI : Projective (S.fgObj p.label) := p.projective
  letI : Epi (S.projectiveSimpleTopProjection p) :=
    S.projectiveSimpleTopProjection_epi p
  apply (finrank_eq_one_iff_of_nonzero'
    (S.projectiveSimpleTopProjection p)
    (S.projectiveSimpleTopProjection_ne_zero p)).2
  intro f
  obtain ⟨g, hg⟩ := Projective.factors f
    (S.projectiveSimpleTopProjection p)
  obtain ⟨c, hc⟩ :=
    S.almostSplitSkeleton.exists_scalar_sub_isRadicalMorphism
      (K := k) p.label g
  have hnot : ¬ IsSplitEpi (g - c • 𝟙 (S.fgObj p.label)) :=
    (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (g - c • 𝟙 (S.fgObj p.label))).1 hc
  obtain ⟨l, hl⟩ :=
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
      p.label p.projective).factors
        (g - c • 𝟙 (S.fgObj p.label)) hnot
  have hzero :
      (g - c • 𝟙 (S.fgObj p.label)) ≫
        S.projectiveSimpleTopProjection p = 0 := by
    rw [← hl, Category.assoc]
    apply FGModuleCat.hom_ext
    ext x
    change (Module.jacobson Aᵐᵒᵖ
      (S.fgObj p.label)).mkQ (l.hom.hom x).1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (l.hom.hom x).2
  refine ⟨c, ?_⟩
  rw [← hg]
  have hdecomp : g = (g - c • 𝟙 (S.fgObj p.label)) +
      c • 𝟙 (S.fgObj p.label) := by abel
  rw [hdecomp, Preadditive.add_comp, hzero, zero_add,
    CategoryTheory.Linear.smul_comp, Category.id_comp]

/-- A complete primitive-projective presentation makes every selected simple
top one-dimensional over the algebraically closed ground field. -/
theorem PrimitiveProjectivePresentation.finrank_projectiveSimpleTop_eq_one
    (P : S.PrimitiveProjectivePresentation) (p : S.ProjectiveLabel) :
    Module.finrank k (S.projectiveSimpleTop p) = 1 := by
  rw [RightModule.finrank_eq_sum_finrank_idempotentCoordinate
    (S.projectiveSimpleTop p) P.idempotent P.complete]
  calc
    ∑ q : S.ProjectiveLabel,
        Module.finrank k
          (RightModule.idempotentCoordinate (k := k)
            (P.idempotent q) (S.projectiveSimpleTop p)) =
      ∑ q : S.ProjectiveLabel, if q = p then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        have hlabel : S.primitiveSourceLabel (P.primitive q) = q.label :=
          congrArg ProjectiveLabel.label (P.sourceLabel q)
        have hcoord :=
          (S.primitiveSourceHomCoordinateEquiv
            (P.primitive q) (S.projectiveSimpleTop p)).finrank_eq
        rw [hlabel] at hcoord
        rw [← hcoord]
        by_cases hqp : q = p
        · subst q
          rw [if_pos rfl]
          exact S.finrank_hom_projectiveSimpleTop_self_eq_one_of_isAlgClosed p
        · rw [if_neg hqp]
          letI : Subsingleton
              (S.fgObj q.label ⟶ S.projectiveSimpleTop p) :=
            ⟨fun f g ↦ by
              rw [S.hom_projectiveSimpleTop_eq_zero p q hqp f,
                S.hom_projectiveSimpleTop_eq_zero p q hqp g]⟩
          exact Module.finrank_zero_of_subsingleton
    _ = 1 := by simp

/-- Every simple right module over an algebra with a complete
primitive-projective presentation is one-dimensional. -/
theorem PrimitiveProjectivePresentation.finrank_eq_one_of_isSimpleModule
    (P : S.PrimitiveProjectivePresentation)
    (X : RightModule.FinitelyGeneratedCategory A)
    (hX : IsSimpleModule Aᵐᵒᵖ X) :
    Module.finrank k X = 1 := by
  letI : Nontrivial X := hX.nontrivial
  obtain ⟨p, hp⟩ := RightModule.exists_positive_idempotentCoordinate
    (k := k) P.idempotent P.complete X
  have hlabel : S.primitiveSourceLabel (P.primitive p) = p.label :=
    congrArg ProjectiveLabel.label (P.sourceLabel p)
  have hcoord :=
    (S.primitiveSourceHomCoordinateEquiv (P.primitive p) X).finrank_eq
  rw [hlabel] at hcoord
  have hhom : 0 < Module.finrank k (S.fgObj p.label ⟶ X) := by
    rwa [hcoord]
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hhom
  have hfLinear : f.hom.hom ≠ 0 := by
    intro hfzero
    apply hf
    apply FGModuleCat.hom_ext
    exact hfzero
  have hsurj : Function.Surjective f.hom.hom :=
    LinearMap.surjective_of_ne_zero hfLinear
  let E : S.projectiveSimpleTop p ≃ₗ[Aᵐᵒᵖ] X :=
    RightModule.moduleTopLinearEquivOfSurjectiveToSimple
      (S.fgObj p.label) X
      (S.projectiveSimpleTop_isSimpleModule p) hX f.hom.hom hsurj
  rw [← (E.restrictScalars k).finrank_eq]
  exact PrimitiveProjectivePresentation.finrank_projectiveSimpleTop_eq_one
    S P p

/-- On a basic algebra presented by a complete primitive family, a
semisimple module of composition length at most two has vector-space
dimension at most two. -/
theorem PrimitiveProjectivePresentation.finrank_le_two_of_semisimple_of_length_le_two
    (P : S.PrimitiveProjectivePresentation)
    (X : RightModule.FinitelyGeneratedCategory A)
    [IsSemisimpleModule Aᵐᵒᵖ X]
    (hle : Module.length Aᵐᵒᵖ X ≤ 2) :
    Module.finrank k X ≤ 2 := by
  by_cases hX : Nontrivial X
  · letI : Nontrivial X := hX
    by_cases htwo : Module.length Aᵐᵒᵖ X = 2
    · obtain ⟨U, V, hU, hV, hcompl⟩ :=
        exists_complementary_simple_of_semisimple_of_length_eq_two htwo
      letI : Module.Finite k X :=
        RightModule.finite_over_field_of_finitelyGenerated k A X
      letI : Module.Finite k U := Module.Finite.of_injective
        (U.subtype.restrictScalars k) U.injective_subtype
      letI : Module.Finite k V := Module.Finite.of_injective
        (V.subtype.restrictScalars k) V.injective_subtype
      let EUV : (U × V) ≃ₗ[k] X :=
        (U.prodEquivOfIsCompl V hcompl).restrictScalars k
      have hUdim : Module.finrank k U = 1 :=
        PrimitiveProjectivePresentation.finrank_eq_one_of_isSimpleModule
          S P (RightModule.submoduleFGObj X U) hU
      have hVdim : Module.finrank k V = 1 :=
        PrimitiveProjectivePresentation.finrank_eq_one_of_isSimpleModule
          S P (RightModule.submoduleFGObj X V) hV
      rw [← EUV.finrank_eq, Module.finrank_prod, hUdim, hVdim]
    · have hsimple : IsSimpleModule Aᵐᵒᵖ X :=
        isSimpleModule_of_nontrivial_of_length_le_two_of_ne_two hle htwo
      rw [PrimitiveProjectivePresentation.finrank_eq_one_of_isSimpleModule
        S P X hsimple]
      omega
  · letI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
    rw [Module.finrank_zero_of_subsingleton]
    omega

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
