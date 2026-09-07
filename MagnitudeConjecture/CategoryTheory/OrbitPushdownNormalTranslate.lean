import MagnitudeConjecture.CategoryTheory.OrbitPushdownCommShift
import MagnitudeConjecture.CategoryTheory.OrbitPushdownResidualFubini
import MagnitudeConjecture.CategoryTheory.ShiftOrbitNormalTranslateShift
import MagnitudeConjecture.CategoryTheory.DeckOrbitNormalTranslateLinear
import MagnitudeConjecture.LinearAlgebra.DirectSumFubini

/-!
# Subgroup orbit push-down and normal translation

For a normal subgroup `N ≤ G`, pushing down an ambient translate of a linear
module along `N` agrees with normally translating its `N`-push-down. Its
direct-sum comparison reindexes `N` by conjugation, so the construction does
not require the ambient deck group to be commutative.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.DirectSumFubini

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Conjugation by `g⁻¹` permutes a normal subgroup. -/
noncomputable def normalSubgroupConjugationEquiv
    (N : Subgroup G) [N.Normal] (g : G) : Additive N ≃ Additive N where
  toFun n := Additive.ofMul
    ⟨g⁻¹ * (n.toMul : G) * g, by
      simpa using ‹N.Normal›.conj_mem n.toMul n.toMul.property g⁻¹⟩
  invFun n := Additive.ofMul
    ⟨g * (n.toMul : G) * g⁻¹, ‹N.Normal›.conj_mem n.toMul n.toMul.property g⟩
  left_inv n := by
    apply Additive.ext
    simp only [toMul_ofMul, Subtype.ext_iff, Subgroup.coe_mk]
    simp [mul_assoc]
  right_inv n := by
    apply Additive.ext
    simp only [toMul_ofMul, Subtype.ext_iff, Subgroup.coe_mk]
    simp [mul_assoc]

@[simp]
theorem normalSubgroupConjugationEquiv_toMul_coe
    (N : Subgroup G) [N.Normal] (g : G) (n : Additive N) :
    (((normalSubgroupConjugationEquiv N g n).toMul : N) : G) =
      g⁻¹ * (n.toMul : G) * g := rfl

@[simp]
theorem normalSubgroupConjugationEquiv_symm_toMul_coe
    (N : Subgroup G) [N.Normal] (g : G) (n : Additive N) :
    ((((normalSubgroupConjugationEquiv N g).symm n).toMul : N) : G) =
      g * (n.toMul : G) * g⁻¹ := rfl

theorem normalSubgroupConjugationEquiv_index
    (N : Subgroup G) [N.Normal] (g : G) (n : Additive N) :
    Additive.ofMul (n.toMul : G) + Additive.ofMul g =
      Additive.ofMul g + Additive.ofMul
        (((normalSubgroupConjugationEquiv N g n).toMul : N) : G) := by
  apply Additive.ext
  simp only [toMul_add, toMul_ofMul,
    normalSubgroupConjugationEquiv_toMul_coe]
  simp [mul_assoc]

/-- The summand of a translated upstairs module indexed by `n` agrees with
the conjugately reindexed summand of the original push-down evaluated at the
ambient inverse translate. -/
noncomputable def orbitPushdownNormalTranslateSummandEquiv
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G)
    (n : Additive N) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := linearModuleCategoryHasShift (k := k) D.core
    ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
        ((shiftFunctor C n).obj X) ≃ₗ[k]
      M.obj.obj ((shiftFunctor C
        (normalSubgroupConjugationEquiv N (-a).toMul n)).obj
          ((shiftFunctor C (-a)).obj X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := linearModuleCategoryHasShift (k := k) D.core
  let b := Additive.ofMul (n.toMul : G)
  let c := Additive.ofMul
    (((normalSubgroupConjugationEquiv N (-a).toMul n).toMul : N) : G)
  change ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
      ((D.core.F b).obj X) ≃ₗ[k]
    M.obj.obj ((D.core.F c).obj ((D.core.F (-a)).obj X))
  have ha : Additive.ofMul (-a).toMul = -a := rfl
  have hbc : b + -a = -a + c := by
    simpa only [b, c, ha] using
      normalSubgroupConjugationEquiv_index N (-a).toMul n
  let e₁ := shiftedOrbitSummandEquiv D.core M a b X
  let e₂ := (M.obj.mapIso
    ((eqToIso (congrArg D.core.F hbc)).app X)).toLinearEquiv
  let e₃ := (M.obj.mapIso ((D.core.add (-a) c).app X)).toLinearEquiv
  exact (e₁.trans e₂).trans e₃

/-- Subgroup push-down intertwines an ambient module translate with
inverse precomposition by the corresponding normal translation of the
subgroup orbit category. -/
noncomputable def orbitPushdownNormalTranslateValueEquiv
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := linearModuleCategoryHasShift (k := k) D.core
    orbitPushdownValue (A := Additive N)
        ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X ≃ₗ[k]
      orbitPushdownValue (A := Additive N) M.obj
        ((shiftFunctor C (-a)).obj X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := linearModuleCategoryHasShift (k := k) D.core
  let e := normalSubgroupConjugationEquiv N (-a).toMul
  let T : Additive N → Type uM := fun n ↦
    ↥(M.obj.obj ((shiftFunctor C n).obj ((shiftFunctor C (-a)).obj X)))
  let S : Additive N → Type uM := fun n ↦
    ↥(((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
      ((shiftFunctor C n).obj X))
  let mapFibers : DirectSum (Additive N) S ≃ₗ[k]
      DirectSum (Additive N) (fun n ↦ T (e n)) :=
    mapRangeLinearEquiv fun n ↦
      D.orbitPushdownNormalTranslateSummandEquiv M N a n X
  let reindex : DirectSum (Additive N) (fun n ↦ T (e n)) ≃ₗ[k]
      DirectSum (Additive N) (fun n ↦ T (e (e.symm n))) :=
    DirectSum.lequivCongrLeft k e
  let castFibers : DirectSum (Additive N) (fun n ↦ T (e (e.symm n))) ≃ₗ[k]
      DirectSum (Additive N) T :=
    mapRangeLinearEquiv fun n ↦
      LinearEquiv.cast (R := k) (M := T) (e.apply_symm_apply n)
  exact (mapFibers.trans reindex).trans castFibers

@[simp]
theorem orbitPushdownNormalTranslateValueEquiv_lof
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G)
    (n : Additive N) (X : C)
    (x : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      letI := linearModuleCategoryHasShift (k := k) D.core
      ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
        ((shiftFunctor C n).obj X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := linearModuleCategoryHasShift (k := k) D.core
    D.orbitPushdownNormalTranslateValueEquiv M N a X
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X n x) =
      orbitPushdownLof M.obj ((shiftFunctor C (-a)).obj X)
        (normalSubgroupConjugationEquiv N (-a).toMul n)
        (D.orbitPushdownNormalTranslateSummandEquiv M N a n X x) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := linearModuleCategoryHasShift (k := k) D.core
  classical
  let e := normalSubgroupConjugationEquiv N (-a).toMul
  let T : Additive N → Type uM := fun m ↦
    ↥(M.obj.obj ((shiftFunctor C m).obj ((shiftFunctor C (-a)).obj X)))
  let S : Additive N → Type uM := fun m ↦
    ↥(((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
      ((shiftFunctor C m).obj X))
  rw [orbitPushdownLof_eq_directSumOf,
    orbitPushdownLof_eq_directSumOf]
  change D.orbitPushdownNormalTranslateValueEquiv M N a X
      (DirectSum.of S n x) =
    DirectSum.of T (e n)
      (D.orbitPushdownNormalTranslateSummandEquiv M N a n X x)
  unfold orbitPushdownNormalTranslateValueEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [mapRangeLinearEquiv_of,
    reindexCastLinearEquiv_of]

/-- Embed subgroup push-down at the inverse ambient translate into full
push-down at the original object. -/
noncomputable def normalTranslateSubgroupPushdownEmbedding
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    orbitPushdownValue (A := Additive N) M.obj
        ((shiftFunctor C (-a)).obj X) →ₗ[k]
      orbitPushdownValue (A := Additive G) M.obj X := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  exact (orbitPushdownMapLinear M.obj
    (shiftOrbitFromShift X (-a))).comp
      (D.subgroupOrbitPushdownValueInclusion M.obj N
        ((shiftFunctor C (-a)).obj X))

/-- Embed subgroup push-down of a translated module into the full push-down
of the original module. -/
noncomputable def shiftedSubgroupPushdownEmbedding
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := linearModuleCategoryHasShift (k := k) D.core
    orbitPushdownValue (A := Additive N)
        ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X →ₗ[k]
      orbitPushdownValue (A := Additive G) M.obj X := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := linearModuleCategoryHasShift (k := k) D.core
  exact (shiftedOrbitPushdownValueEquiv D.core M a X).toLinearMap.comp
    (D.subgroupOrbitPushdownValueInclusion
      ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) N X)

/-- The normal-translation equivalence is the unique reindexing compatible
with the two canonical inclusions into full ambient push-down. -/
theorem normalTranslateSubgroupPushdownEmbedding_comp_equiv
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := linearModuleCategoryHasShift (k := k) D.core
    (D.normalTranslateSubgroupPushdownEmbedding M N a X).comp
        (D.orbitPushdownNormalTranslateValueEquiv M N a X).toLinearMap =
      D.shiftedSubgroupPushdownEmbedding M N a X := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := linearModuleCategoryHasShift (k := k) D.core
  classical
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  unfold normalTranslateSubgroupPushdownEmbedding
  unfold shiftedSubgroupPushdownEmbedding
  simp only [LinearMap.comp_apply]
  rw [DirectSum.lof_eq_of]
  rw [← orbitPushdownLof_eq_directSumOf]
  change orbitPushdownMapLinear M.obj (shiftOrbitFromShift X (-a))
      (D.subgroupOrbitPushdownValueInclusion M.obj N
        ((shiftFunctor C (-a)).obj X)
        (D.orbitPushdownNormalTranslateValueEquiv M N a X
          (orbitPushdownLof
            ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X n x))) =
    shiftedOrbitPushdownValueEquiv D.core M a X
      (D.subgroupOrbitPushdownValueInclusion
        ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) N X
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X n x))
  rw [D.orbitPushdownNormalTranslateValueEquiv_lof,
    subgroupOrbitPushdownValueInclusion_lof,
    subgroupOrbitPushdownValueInclusion_lof,
    shiftedOrbitPushdownValueEquiv_lof]
  unfold shiftOrbitFromShift
  rw [orbitPushdownMapLinear_of,
    orbitPushdownHomogeneousMap_lof]
  let b := Additive.ofMul (n.toMul : G)
  let c := Additive.ofMul
    (((normalSubgroupConjugationEquiv N (-a).toMul n).toMul : N) : G)
  have hbc : b + -a = -a + c := by
    have ha : Additive.ofMul (-a).toMul = -a := rfl
    simpa only [b, c, ha] using
      normalSubgroupConjugationEquiv_index N (-a).toMul n
  let z := D.orbitPushdownNormalTranslateSummandEquiv M N a n X x
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext hbc.symm
  apply (orbitPushdownComponent_apply_heq_component'_apply M.obj
    hbc.symm (𝟙 ((shiftFunctor C (-a)).obj X)) z).trans
  apply heq_of_eq
  unfold z orbitPushdownNormalTranslateSummandEquiv
  unfold orbitPushdownComponent'
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    Functor.mapIso_hom]
  simp only [orbitPushdownArrow', shiftFunctorAdd', Iso.trans_inv, NatTrans.comp_app,
    D.core.shiftFunctorAdd_eq, D.core.shiftFunctor_eq, id_eq]
  rw [(D.core.F c).map_id, Category.id_comp]
  let eEq := (eqToIso (congrArg D.core.F hbc)).app X
  let eAdd := (D.core.add (-a) c).app X
  let y := shiftedOrbitSummandEquiv D.core M a b X x
  change (M.obj.map eEq.hom ≫ M.obj.map eAdd.hom ≫
    M.obj.map (eAdd.inv ≫ eEq.inv)) y = y
  rw [← M.obj.map_comp, ← M.obj.map_comp]
  simp

/-- The ambient summand belonging to a subgroup degree is canonically the
corresponding summand for the restricted shift. -/
noncomputable def subgroupOrbitPushdownSummandEquiv
    (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]
    (N : Subgroup G) (X : C) (n : Additive N) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    M.obj ((shiftFunctor C (Additive.ofMul (n.toMul : G))).obj X) ≃ₗ[k]
      M.obj ((shiftFunctor C n).obj X) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  change M.obj ((D.core.F (Additive.ofMul (n.toMul : G))).obj X) ≃ₗ[k]
    M.obj ((D.core.F (Additive.ofMul (n.toMul : G))).obj X)
  exact LinearEquiv.refl k _

/-- Project an ambient push-down value onto the component indexed by a
specified subgroup degree. -/
noncomputable def subgroupOrbitPushdownValueProjectionComponent
    (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]
    (N : Subgroup G) (X : C) (n : Additive N) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    orbitPushdownValue (A := Additive G) M X →ₗ[k]
      M.obj ((shiftFunctor C n).obj X) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  exact (D.subgroupOrbitPushdownSummandEquiv M N X n).toLinearMap.comp
    (DirectSum.component k (Additive G)
      (fun g ↦ M.obj ((shiftFunctor C g).obj X))
      (Additive.ofMul (n.toMul : G)))

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k] in
/-- Projecting extension by zero onto a subgroup component is the original
direct-sum component. -/
theorem subgroupOrbitPushdownValueProjectionComponent_comp_inclusion
    (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]
    (N : Subgroup G) (X : C) (n : Additive N) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    (D.subgroupOrbitPushdownValueProjectionComponent M N X n).comp
        (D.subgroupOrbitPushdownValueInclusion M N X) =
      DirectSum.component k (Additive N)
        (fun m ↦ M.obj ((shiftFunctor C m).obj X)) n := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  classical
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [DirectSum.lof_eq_of, ← orbitPushdownLof_eq_directSumOf]
  rw [subgroupOrbitPushdownValueInclusion_lof]
  unfold subgroupOrbitPushdownValueProjectionComponent
  simp only [LinearMap.comp_apply]
  by_cases hmn : m = n
  · subst n
    simp [orbitPushdownLof,
      subgroupOrbitPushdownSummandEquiv]
    rfl
  · have hcoerce : Additive.ofMul (m.toMul : G) ≠
        Additive.ofMul (n.toMul : G) := by
      intro h
      apply hmn
      apply Additive.toMul.injective
      apply Subtype.ext
      exact Additive.ofMul.injective h
    simp [orbitPushdownLof, DirectSum.component.of, hmn, hcoerce]

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k] in
/-- Extension by zero from subgroup-indexed values into ambient-indexed
values is injective. -/
theorem subgroupOrbitPushdownValueInclusion_injective
    (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]
    (N : Subgroup G) (X : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    Function.Injective (D.subgroupOrbitPushdownValueInclusion M N X) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  classical
  intro x y hxy
  apply DFinsupp.ext
  intro n
  have hcomponent := congrArg
    (D.subgroupOrbitPushdownValueProjectionComponent M N X n) hxy
  have hprojection :=
    D.subgroupOrbitPushdownValueProjectionComponent_comp_inclusion M N X n
  exact LinearMap.congr_fun hprojection x ▸
    LinearMap.congr_fun hprojection y ▸ hcomponent

/-- The comparison embedding of the normally translated subgroup
push-down is injective. -/
theorem normalTranslateSubgroupPushdownEmbedding_injective
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    Function.Injective
      (D.normalTranslateSubgroupPushdownEmbedding M N a X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  let e := (orbitPushdown (A := Additive G) M.obj).mapIso
    (ShiftOrbitCategory.objectShiftIso X (-a))
  intro x y hxy
  apply D.subgroupOrbitPushdownValueInclusion_injective M.obj N
    ((shiftFunctor C (-a)).obj X)
  apply e.symm.toLinearEquiv.injective
  exact hxy

/-- Ambient inclusion turns a normally translated subgroup path followed by
the canonical return path into the original subgroup path preceded by the
canonical return path. -/
theorem shiftOrbitNormalTranslate_subgroup_path
    (N : Subgroup G) [N.Normal] (g : G) {X Y : C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    shiftOrbitCompHom
        (D.shiftOrbitSubgroupMap N _ _
          (D.shiftOrbitNormalTranslateMap N g f))
        (shiftOrbitFromShift Y (Additive.ofMul g)) =
      shiftOrbitCompHom
        (shiftOrbitFromShift X (Additive.ofMul g))
        (D.shiftOrbitSubgroupMap N X Y f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  rw [D.shiftOrbitSubgroupMap_normalTranslateMap]
  unfold shiftOrbitAmbientConjugate
  change ((ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)).inv ≫
      D.shiftOrbitSubgroupMap N X Y f ≫
        (ShiftOrbitCategory.objectShiftIso Y (Additive.ofMul g)).hom) ≫
      (ShiftOrbitCategory.objectShiftIso Y (Additive.ofMul g)).inv =
    (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)).inv ≫
      D.shiftOrbitSubgroupMap N X Y f
  simp

/-- Normal translation with its ambient degree kept in additive form.  This
wrapper exposes literal source and target objects to later module formulas. -/
noncomputable def shiftOrbitNormalTranslateMapAdditive
    (N : Subgroup G) [N.Normal] (b : Additive G) {X Y : C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N)
      ((shiftFunctor C b).obj X) ((shiftFunctor C b).obj Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  change ShiftOrbitHom (Additive N)
    ((D.core.F b).obj X) ((D.core.F b).obj Y)
  exact D.shiftOrbitNormalTranslateMap N b.toMul f

/-- The fixed normal-translation functor with its degree represented
literally in `Additive G`. -/
noncomputable def shiftOrbitNormalTranslateFunctorAdditive
    (N : Subgroup G) [N.Normal] (b : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitCategory C (Additive N) ⥤
      ShiftOrbitCategory C (Additive N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact
    { obj := fun X ↦ (shiftFunctor C b).obj (show C from X)
      map := fun {X Y} f ↦ D.shiftOrbitNormalTranslateMapAdditive N b f
      map_id := by
        intro X
        change (D.shiftOrbitNormalTranslateFunctor N b.toMul).map (𝟙 X) = 𝟙 _
        exact (D.shiftOrbitNormalTranslateFunctor N b.toMul).map_id X
      map_comp := by
        intro X Y Z f h
        change (D.shiftOrbitNormalTranslateFunctor N b.toMul).map (f ≫ h) =
          (D.shiftOrbitNormalTranslateFunctor N b.toMul).map f ≫
            (D.shiftOrbitNormalTranslateFunctor N b.toMul).map h
        exact (D.shiftOrbitNormalTranslateFunctor N b.toMul).map_comp f h }

instance shiftOrbitNormalTranslateFunctorAdditive_additive
    (N : Subgroup G) [N.Normal] (b : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.shiftOrbitNormalTranslateFunctorAdditive N b).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  constructor
  intro X Y f h
  change (D.shiftOrbitNormalTranslateFunctor N b.toMul).map (f + h) = _
  rw [Functor.map_add]
  rfl

instance shiftOrbitNormalTranslateFunctorAdditive_linear
    (N : Subgroup G) [N.Normal] (b : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.shiftOrbitNormalTranslateFunctorAdditive N b).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  constructor
  intro X Y f r
  change (D.shiftOrbitNormalTranslateFunctor N b.toMul).map (r • f) = _
  rw [Functor.map_smul]
  rfl

/-- The additive-degree wrapper satisfies the same ambient path identity. -/
theorem shiftOrbitNormalTranslateAdditive_subgroup_path
    (N : Subgroup G) [N.Normal] (b : Additive G) {X Y : C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    shiftOrbitCompHom
        (D.shiftOrbitSubgroupMap N _ _
          (D.shiftOrbitNormalTranslateMapAdditive N b f))
        (shiftOrbitFromShift Y b) =
      shiftOrbitCompHom (shiftOrbitFromShift X b)
        (D.shiftOrbitSubgroupMap N X Y f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  change shiftOrbitCompHom
      (D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateMap N b.toMul f))
      (shiftOrbitFromShift Y (Additive.ofMul b.toMul)) = _
  exact D.shiftOrbitNormalTranslate_subgroup_path N b.toMul f

/-- The normally translated subgroup embedding is natural for subgroup
orbit morphisms. -/
theorem normalTranslateSubgroupPushdownEmbedding_naturality
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) {X Y : C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.normalTranslateSubgroupPushdownEmbedding M N a Y).comp
        (orbitPushdownMapLinear M.obj
          (D.shiftOrbitNormalTranslateMapAdditive N (-a) f)) =
      (orbitPushdownMapLinear M.obj
        (D.shiftOrbitSubgroupMap N X Y f)).comp
          (D.normalTranslateSubgroupPushdownEmbedding M N a X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  unfold normalTranslateSubgroupPushdownEmbedding
  rw [LinearMap.comp_assoc]
  rw [D.subgroupOrbitPushdownValueInclusion_naturality M.obj N _ _
    (D.shiftOrbitNormalTranslateMapAdditive N (-a) f)]
  rw [← LinearMap.comp_assoc]
  rw [← orbitPushdownMapLinear_comp]
  rw [D.shiftOrbitNormalTranslateAdditive_subgroup_path N (-a) f]
  rw [orbitPushdownMapLinear_comp]
  rfl

/-- The embedding of subgroup push-down for a translated upstairs module is
natural for subgroup orbit morphisms. -/
theorem shiftedSubgroupPushdownEmbedding_naturality
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) {X Y : C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
      (M⟦a⟧).property.1
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
      (M⟦a⟧).property.2
    (D.shiftedSubgroupPushdownEmbedding M N a Y).comp
        (orbitPushdownMapLinear
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) f) =
      (orbitPushdownMapLinear M.obj
        (D.shiftOrbitSubgroupMap N X Y f)).comp
          (D.shiftedSubgroupPushdownEmbedding M N a X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
    (M⟦a⟧).property.1
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
    (M⟦a⟧).property.2
  unfold shiftedSubgroupPushdownEmbedding
  rw [LinearMap.comp_assoc]
  rw [D.subgroupOrbitPushdownValueInclusion_naturality
    ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) N X Y f]
  rw [← LinearMap.comp_assoc]
  rw [shiftedOrbitPushdownValueEquiv_naturality D.core M a
    (D.shiftOrbitSubgroupMap N X Y f)]
  rfl

/-- The direct-sum normal-translation equivalence is natural for every
subgroup orbit morphism. -/
theorem orbitPushdownNormalTranslateValueEquiv_naturality
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) {X Y : C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
      (M⟦a⟧).property.1
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
      (M⟦a⟧).property.2
    (D.orbitPushdownNormalTranslateValueEquiv M N a Y).toLinearMap.comp
        (orbitPushdownMapLinear
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) f) =
      (orbitPushdownMapLinear M.obj
        (D.shiftOrbitNormalTranslateMapAdditive N (-a) f)).comp
          (D.orbitPushdownNormalTranslateValueEquiv M N a X).toLinearMap := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
    (M⟦a⟧).property.1
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
    (M⟦a⟧).property.2
  apply LinearMap.ext
  intro x
  apply D.normalTranslateSubgroupPushdownEmbedding_injective M N a Y
  let eX := D.orbitPushdownNormalTranslateValueEquiv M N a X
  let eY := D.orbitPushdownNormalTranslateValueEquiv M N a Y
  let JX := D.normalTranslateSubgroupPushdownEmbedding M N a X
  let JY := D.normalTranslateSubgroupPushdownEmbedding M N a Y
  let KX := D.shiftedSubgroupPushdownEmbedding M N a X
  let KY := D.shiftedSubgroupPushdownEmbedding M N a Y
  let sf := orbitPushdownMapLinear
    ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) f
  let nf := orbitPushdownMapLinear M.obj
    (D.shiftOrbitNormalTranslateMapAdditive N (-a) f)
  let af := orbitPushdownMapLinear M.obj
    (D.shiftOrbitSubgroupMap N X Y f)
  calc
    JY (eY (sf x)) = KY (sf x) := by
      exact LinearMap.congr_fun
        (D.normalTranslateSubgroupPushdownEmbedding_comp_equiv M N a Y)
        (sf x)
    _ = af (KX x) := by
      exact LinearMap.congr_fun
        (D.shiftedSubgroupPushdownEmbedding_naturality M N a f) x
    _ = af (JX (eX x)) := by
      apply congrArg af
      exact (LinearMap.congr_fun
        (D.normalTranslateSubgroupPushdownEmbedding_comp_equiv M N a X)
        x).symm
    _ = JY (nf (eX x)) := by
      symm
      exact LinearMap.congr_fun
        (D.normalTranslateSubgroupPushdownEmbedding_naturality M N a f)
        (eX x)

/-- Subgroup push-down of an ambient module translate is naturally the
normal translate of subgroup push-down. -/
noncomputable def orbitPushdownNormalTranslateIso
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
      (M⟦a⟧).property.1
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
      (M⟦a⟧).property.2
    orbitPushdown (A := Additive N)
        ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) ≅
      D.shiftOrbitNormalTranslateFunctorAdditive N (-a) ⋙
        orbitPushdown (A := Additive N) M.obj := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
    (M⟦a⟧).property.1
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
    (M⟦a⟧).property.2
  exact NatIso.ofComponents
    (fun X ↦ (D.orbitPushdownNormalTranslateValueEquiv M N a
      (show C from X)).toModuleIso)
    (fun {X Y} f ↦ by
      apply ModuleCat.hom_ext
      change
        (D.orbitPushdownNormalTranslateValueEquiv M N a
          (show C from Y)).toLinearMap.comp
            (orbitPushdownMapLinear
              ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) f) =
          (orbitPushdownMapLinear M.obj
            (D.shiftOrbitNormalTranslateMapAdditive N (-a) f)).comp
              (D.orbitPushdownNormalTranslateValueEquiv M N a
                (show C from X)).toLinearMap
      exact D.orbitPushdownNormalTranslateValueEquiv_naturality M N a f)

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
