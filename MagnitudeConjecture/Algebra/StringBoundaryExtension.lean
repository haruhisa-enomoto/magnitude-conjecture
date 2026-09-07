import MagnitudeConjecture.Algebra.StringPrefixExtension

/-!
# String maps controlled by the first extension letter

For an arbitrary right extension, the first new letter controls the module
map across the old/new coordinate boundary.  A negative first letter makes
the old positions a subrepresentation, while a positive first letter makes
their coordinate projection a quotient representation.  Later letters may
have either sign.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

namespace NegativeBoundaryExtension

/-- If the first appended letter is negative, every displayed-arrow output
from an inherited position is still inherited, even after an arbitrary
further tail. -/
theorem exists_old_of_arrowStep
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    {x y : Q} (b : x ⟶ y) (i : C.PositionAt x) (l : D.PositionAt y)
    (hil : D.ArrowStep b (extension.toRightExtension.position i) l) :
    ∃ j : C.PositionAt y,
      extension.toRightExtension.position j = l := by
  have hlBound : l.index ≤
      (append R C (negativeArrow extension.arrow)
        extension.valid).length := by
    have hindex := hil.index
    have hiUpper := i.index_le
    rw [append_length]
    rcases hindex with hforward | hbackward
    · rw [extension.toRightExtension.position_index] at hforward
      omega
    · rw [extension.toRightExtension.position_index] at hbackward
      omega
  rcases extension.tail.exists_eq_position_of_index_le l hlBound with
    ⟨q, hq⟩
  have hilBase :
      (append R C (negativeArrow extension.arrow) extension.valid).ArrowStep
        b (appendPosition C (negativeArrow extension.arrow)
          extension.valid i) q := by
    apply (extension.tail.arrowStep_position_iff b _ _).1
    rw [extension.toRightExtension_position] at hil
    rw [← hq] at hil
    exact hil
  rcases exists_old_of_arrowStep_appendPosition_negative
      C extension.arrow extension.valid b i q hilBase with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [extension.toRightExtension_position, hj, hq]

/-- The coordinate inclusion for a negative-boundary extension commutes with
every displayed-arrow action. -/
theorem spaceInclusion_arrowLinearMap
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    {x y : Q} (b : x ⟶ y) (v : C.Space x) :
    extension.toRightExtension.spaceInclusion y (C.arrowLinearMap b v) =
      D.arrowLinearMap b
        (extension.toRightExtension.spaceInclusion x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul,
        map_smul]
      classical
      by_cases hex : ∃ j : C.PositionAt y, C.ArrowStep b i j
      · let j := Classical.choose hex
        have hij : C.ArrowStep b i j := Classical.choose_spec hex
        rw [C.arrowLinearMap_single_one_of_step b i j hij,
          extension.toRightExtension.spaceInclusion_single,
          extension.toRightExtension.spaceInclusion_single]
        symm
        rw [D.arrowLinearMap_single_one_of_step b
          (extension.toRightExtension.position i)
          (extension.toRightExtension.position j)
          (extension.toRightExtension.arrowStep_position b i j hij)]
      · rw [C.arrowLinearMap_single, one_smul,
          C.arrowOnBasis_eq_zero_of_not_exists b i hex, map_zero,
          extension.toRightExtension.spaceInclusion_single,
          D.arrowLinearMap_single, one_smul]
        symm
        rw [D.arrowOnBasis_eq_zero_of_not_exists]
        rintro ⟨l, hil⟩
        rcases extension.exists_old_of_arrowStep b i l hil with ⟨j, hj⟩
        apply hex
        refine ⟨j, ?_⟩
        apply (extension.toRightExtension.arrowStep_position_iff b i j).1
        rwa [hj]

/-- A negative-boundary prefix inclusion is a morphism of quiver
representations. -/
def quiverRepresentationInclusion
    {C D : Word R} (extension : NegativeBoundaryExtension C D) :
    C.quiverRepresentation ⟶ D.quiverRepresentation :=
  Paths.liftNatTrans
    (fun x ↦ ModuleCat.ofHom
      (extension.toRightExtension.spaceInclusion x))
    (fun {x y} b ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change extension.toRightExtension.spaceInclusion y
          (C.arrowLinearMap b v) =
        D.arrowLinearMap b
          (extension.toRightExtension.spaceInclusion x v)
      exact extension.spaceInclusion_arrowLinearMap b v)

/-- In the opposite-module realization, the negative-boundary inclusion has
the reversed natural-transformation direction. -/
def freeRightModuleAuxInclusion
    {C D : Word R} (extension : NegativeBoundaryExtension C D) :
    D.freeRightModuleAux ⟶ C.freeRightModuleAux :=
  LinearPathCategory.liftNatTrans
    (fun x ↦ Opposite.op (ModuleCat.of k (D.Space x)))
    (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
    (fun b ↦ (ModuleCat.ofHom (D.arrowLinearMap b)).op)
    (fun b ↦ (ModuleCat.ofHom (C.arrowLinearMap b)).op)
    (fun x ↦ (ModuleCat.ofHom
      (extension.toRightExtension.spaceInclusion x)).op)
    (fun {x y} b ↦ by
      rw [← op_comp, ← op_comp]
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change D.arrowLinearMap b
          (extension.toRightExtension.spaceInclusion x v) =
        extension.toRightExtension.spaceInclusion y
          (C.arrowLinearMap b v)
      exact (extension.spaceInclusion_arrowLinearMap b v).symm)

/-- Descend the negative-boundary inclusion through the monomial relation
quotient. -/
def quotientRightModuleAuxInclusion
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    D.quotientRightModuleAux hmono ⟶ C.quotientRightModuleAux hmono :=
  HomIdeal.quotientLiftNatTrans
    (k := k)
    (I := LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (F := D.freeRightModuleAux)
    (D.relationIdeal_isKilledBy hmono)
    (C.relationIdeal_isKilledBy hmono)
    extension.freeRightModuleAuxInclusion

/-- The canonical inclusion associated to any extension whose first letter
is negative, as a morphism of right modules. -/
def rightModuleInclusion
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    C.rightModule hmono ⟶ D.rightModule hmono where
  app X := ((extension.quotientRightModuleAuxInclusion hmono).app
    X.unop).unop
  naturality {X Y} f := by
    apply Quiver.Hom.op_inj
    exact ((extension.quotientRightModuleAuxInclusion hmono).naturality
      f.unop).symm

@[simp]
theorem rightModuleInclusion_app_obj
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) (x : Q) :
    (extension.rightModuleInclusion hmono).app
        (Opposite.op (obj R x)) =
      ModuleCat.ofHom (extension.toRightExtension.spaceInclusion x) :=
  rfl

/-- A negative-boundary map is a submodule inclusion. -/
instance rightModuleInclusion_mono
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    Mono (extension.rightModuleInclusion hmono) := by
  haveI hmonoApp (X : (Category R)ᵒᵖ) :
      Mono ((extension.rightModuleInclusion hmono).app X) := by
    rw [ModuleCat.mono_iff_injective]
    exact extension.toRightExtension.spaceInclusion_injective X.unop.as
  exact NatTrans.mono_of_mono_app _

/-- Negative-boundary inclusions compose under further negative-boundary
extension. -/
theorem rightModuleInclusion_transRightExtension
    {C D E : Word R}
    (first : NegativeBoundaryExtension C D)
    (second : NegativeBoundaryExtension D E)
    (hmono : IsMonomial R) :
    (first.transRightExtension second.toRightExtension).rightModuleInclusion
        hmono =
      first.rightModuleInclusion hmono ≫ second.rightModuleInclusion hmono := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change
    (first.transRightExtension second.toRightExtension).toRightExtension.spaceInclusion
        X.unop.as v =
      second.toRightExtension.spaceInclusion X.unop.as
        (first.toRightExtension.spaceInclusion X.unop.as v)
  rw [toRightExtension_transRightExtension,
    RightExtension.spaceInclusion_trans_apply]

end NegativeBoundaryExtension

namespace PositiveBoundaryExtension

/-- If the first appended letter is positive, no arrow action can travel
from a non-inherited position back into an inherited position. -/
theorem not_arrowStep_to_old_of_not_old
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    {x y : Q} (b : x ⟶ y) (j : D.PositionAt x) (i : C.PositionAt y)
    (hj : ¬ ∃ q : C.PositionAt x,
      extension.toRightExtension.position q = j) :
    ¬ D.ArrowStep b j (extension.toRightExtension.position i) := by
  intro hji
  have hjBound : j.index ≤
      (append R C (positiveArrow extension.arrow)
        extension.valid).length := by
    have hindex := hji.index
    have hiUpper := i.index_le
    rw [append_length]
    rcases hindex with hforward | hbackward
    · rw [extension.toRightExtension.position_index] at hforward
      omega
    · rw [extension.toRightExtension.position_index] at hbackward
      omega
  rcases extension.tail.exists_eq_position_of_index_le j hjBound with
    ⟨q, hq⟩
  have hqNotOld : ¬ ∃ r : C.PositionAt x,
      appendPosition C (positiveArrow extension.arrow)
        extension.valid r = q := by
    rintro ⟨r, hr⟩
    apply hj
    refine ⟨r, ?_⟩
    rw [extension.toRightExtension_position, hr, hq]
  have hqNotLe : ¬ q.index ≤ C.length := by
    intro hqLe
    exact hqNotOld (exists_eq_appendPosition_of_index_le
      C (positiveArrow extension.arrow) extension.valid q hqLe)
  have hqFinal : q.index =
      (append R C (positiveArrow extension.arrow)
        extension.valid).length := by
    rw [append_length]
    have hqUpper := q.index_le
    rw [append_length] at hqUpper
    omega
  have hx := q.eq_target_of_index_eq_length hqFinal
  have hxQ : x = extension.vertex := hx
  subst x
  have hqEnd : q = appendEndPosition C
      (positiveArrow extension.arrow) extension.valid :=
    eq_appendEndPosition_of_not_exists_old C
      (positiveArrow extension.arrow) extension.valid q hqNotOld
  have hjiBase :
      (append R C (positiveArrow extension.arrow) extension.valid).ArrowStep
        b q (appendPosition C (positiveArrow extension.arrow)
          extension.valid i) := by
    apply (extension.tail.arrowStep_position_iff b _ _).1
    rw [extension.toRightExtension_position] at hji
    rw [← hq] at hji
    exact hji
  apply not_exists_arrowStep_appendEndPosition_positive
    C extension.arrow extension.valid b
  exact ⟨appendPosition C (positiveArrow extension.arrow)
    extension.valid i, by rwa [← hqEnd]⟩

/-- The coordinate projection for a positive-boundary extension commutes
with every displayed-arrow action. -/
theorem spaceProjection_arrowLinearMap
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    {x y : Q} (b : x ⟶ y) (v : D.Space x) :
    extension.toRightExtension.spaceProjection y (D.arrowLinearMap b v) =
      C.arrowLinearMap b
        (extension.toRightExtension.spaceProjection x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single j c =>
      rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul,
        map_smul]
      classical
      by_cases hjOld : ∃ i : C.PositionAt x,
          extension.toRightExtension.position i = j
      · rcases hjOld with ⟨i, rfl⟩
        rw [extension.toRightExtension.spaceProjection_single_position]
        by_cases hex : ∃ l : C.PositionAt y, C.ArrowStep b i l
        · let l := Classical.choose hex
          have hil : C.ArrowStep b i l := Classical.choose_spec hex
          rw [D.arrowLinearMap_single_one_of_step b
              (extension.toRightExtension.position i)
              (extension.toRightExtension.position l)
              (extension.toRightExtension.arrowStep_position b i l hil),
            extension.toRightExtension.spaceProjection_single_position,
            C.arrowLinearMap_single_one_of_step b i l hil]
        · rw [C.arrowLinearMap_single, one_smul,
            C.arrowOnBasis_eq_zero_of_not_exists b i hex]
          rw [D.arrowLinearMap_single, one_smul]
          by_cases hext : ∃ l : D.PositionAt y,
              D.ArrowStep b (extension.toRightExtension.position i) l
          · let l := Classical.choose hext
            have hil := Classical.choose_spec hext
            rw [D.arrowOnBasis_eq_single_of_step b
              (extension.toRightExtension.position i) l hil]
            rw [extension.toRightExtension.spaceProjection_single_of_not_exists
              l 1 (by
                rintro ⟨q, hq⟩
                apply hex
                refine ⟨q, ?_⟩
                apply (extension.toRightExtension.arrowStep_position_iff
                  b i q).1
                rwa [hq])]
          · rw [D.arrowOnBasis_eq_zero_of_not_exists b
              (extension.toRightExtension.position i) hext, map_zero]
      · rw [extension.toRightExtension.spaceProjection_single_of_not_exists
          j 1 hjOld, map_zero]
        rw [D.arrowLinearMap_single, one_smul]
        by_cases hext : ∃ l : D.PositionAt y, D.ArrowStep b j l
        · let l := Classical.choose hext
          have hjl := Classical.choose_spec hext
          rw [D.arrowOnBasis_eq_single_of_step b j l hjl]
          rw [extension.toRightExtension.spaceProjection_single_of_not_exists
            l 1 (by
              rintro ⟨i, hi⟩
              exact extension.not_arrowStep_to_old_of_not_old b j i hjOld
                (by rwa [hi]))]
        · rw [D.arrowOnBasis_eq_zero_of_not_exists b j hext, map_zero]

/-- A positive-boundary coordinate projection is a morphism of quiver
representations. -/
def quiverRepresentationProjection
    {C D : Word R} (extension : PositiveBoundaryExtension C D) :
    D.quiverRepresentation ⟶ C.quiverRepresentation :=
  Paths.liftNatTrans
    (fun x ↦ ModuleCat.ofHom
      (extension.toRightExtension.spaceProjection x))
    (fun {x y} b ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change extension.toRightExtension.spaceProjection y
          (D.arrowLinearMap b v) =
        C.arrowLinearMap b
          (extension.toRightExtension.spaceProjection x v)
      exact extension.spaceProjection_arrowLinearMap b v)

/-- In the opposite-module realization, the positive-boundary projection has
the reversed natural-transformation direction. -/
def freeRightModuleAuxProjection
    {C D : Word R} (extension : PositiveBoundaryExtension C D) :
    C.freeRightModuleAux ⟶ D.freeRightModuleAux :=
  LinearPathCategory.liftNatTrans
    (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
    (fun x ↦ Opposite.op (ModuleCat.of k (D.Space x)))
    (fun b ↦ (ModuleCat.ofHom (C.arrowLinearMap b)).op)
    (fun b ↦ (ModuleCat.ofHom (D.arrowLinearMap b)).op)
    (fun x ↦ (ModuleCat.ofHom
      (extension.toRightExtension.spaceProjection x)).op)
    (fun {x y} b ↦ by
      rw [← op_comp, ← op_comp]
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change C.arrowLinearMap b
          (extension.toRightExtension.spaceProjection x v) =
        extension.toRightExtension.spaceProjection y
          (D.arrowLinearMap b v)
      exact (extension.spaceProjection_arrowLinearMap b v).symm)

/-- Descend the positive-boundary projection through the monomial relation
quotient. -/
def quotientRightModuleAuxProjection
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    C.quotientRightModuleAux hmono ⟶ D.quotientRightModuleAux hmono :=
  HomIdeal.quotientLiftNatTrans
    (k := k)
    (I := LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (F := C.freeRightModuleAux)
    (C.relationIdeal_isKilledBy hmono)
    (D.relationIdeal_isKilledBy hmono)
    extension.freeRightModuleAuxProjection

/-- The canonical projection associated to any extension whose first letter
is positive, as a morphism of right modules. -/
def rightModuleProjection
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶ C.rightModule hmono where
  app X := ((extension.quotientRightModuleAuxProjection hmono).app
    X.unop).unop
  naturality {X Y} f := by
    apply Quiver.Hom.op_inj
    exact ((extension.quotientRightModuleAuxProjection hmono).naturality
      f.unop).symm

@[simp]
theorem rightModuleProjection_app_obj
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) (x : Q) :
    (extension.rightModuleProjection hmono).app
        (Opposite.op (obj R x)) =
      ModuleCat.ofHom (extension.toRightExtension.spaceProjection x) :=
  rfl

/-- A positive-boundary map is a quotient projection. -/
instance rightModuleProjection_epi
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    Epi (extension.rightModuleProjection hmono) := by
  haveI hepiApp (X : (Category R)ᵒᵖ) :
      Epi ((extension.rightModuleProjection hmono).app X) := by
    rw [ModuleCat.epi_iff_surjective]
    exact extension.toRightExtension.spaceProjection_surjective X.unop.as
  exact NatTrans.epi_of_epi_app _

/-- Positive-boundary projections compose under further positive-boundary
extension. -/
theorem rightModuleProjection_transRightExtension
    {C D E : Word R}
    (first : PositiveBoundaryExtension C D)
    (second : PositiveBoundaryExtension D E)
    (hmono : IsMonomial R) :
    (first.transRightExtension second.toRightExtension).rightModuleProjection
        hmono =
      second.rightModuleProjection hmono ≫ first.rightModuleProjection hmono := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change
    (first.transRightExtension second.toRightExtension).toRightExtension.spaceProjection
        X.unop.as v =
      first.toRightExtension.spaceProjection X.unop.as
        (second.toRightExtension.spaceProjection X.unop.as v)
  rw [toRightExtension_transRightExtension,
    RightExtension.spaceProjection_trans_apply]

end PositiveBoundaryExtension

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
