import MagnitudeConjecture.CategoryTheory.MeshPairedRelation
import MagnitudeConjecture.CategoryTheory.MeshIdealEndpoint
import MagnitudeConjecture.CategoryTheory.MeshPositiveTail

/-!
# The translation map in a mesh-simple presentation

At a nonprojective vertex, the polarization sends every incoming arrow to the
paired arrow out of the translate.  Precomposition with these paired arrows
defines the map preceding the incoming-arrow map in the standard projective
presentation of the vertex simple.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- The free-category paired coefficient family before imposing the mesh
relations. -/
def freePairedCoefficient
    (z : {z : Q // z ∉ T.projective}) {x : Q}
    (q : MagnitudeConjecture.LinearPathCategory.obj k Q x ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q (T.tau z)) :
    MagnitudeConjecture.LinearPathCategory.IncomingCoefficient
      (k := k) x z.1 :=
  fun a ↦ q ≫ MagnitudeConjecture.LinearPathCategory.pathHom
    ((T.arrowEquiv z a.1) a.2).toPath

/-- Quotienting a free incoming sum gives the corresponding incoming sum in
the mesh category. -/
theorem quotient_map_free_incomingSum {x z : Q}
    (c : MagnitudeConjecture.LinearPathCategory.IncomingCoefficient
      (k := k) x z) :
    (quotientFunctor (k := k) T).map
        (MagnitudeConjecture.LinearPathCategory.incomingSum c) =
      T.incomingSum (k := k)
        (fun a ↦ (quotientFunctor (k := k) T).map (c a)) := by
  rw [MagnitudeConjecture.LinearPathCategory.incomingSum, incomingSum,
    (quotientFunctor (k := k) T).map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(quotientFunctor (k := k) T).map_comp]
  rfl

/-- Coefficients obtained by following a morphism to the translate by every
paired arrow. -/
def pairedCoefficient
    (z : {z : Q // z ∉ T.projective}) {x : Q}
    (q : obj (k := k) T x ⟶ obj (k := k) T (T.tau z)) :
    IncomingCoefficient (k := k) T x z.1 :=
  fun a ↦ q ≫ T.incomingArrowHom (k := k)
    (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1)

/-- Quotienting one free paired coefficient gives the corresponding paired
coefficient in the mesh category. -/
theorem quotient_map_freePairedCoefficient_apply
    (z : {z : Q // z ∉ T.projective}) {x : Q}
    (q : MagnitudeConjecture.LinearPathCategory.obj k Q x ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q (T.tau z))
    (a : MagnitudeConjecture.LinearPathCategory.IncomingArrow z.1) :
    (quotientFunctor (k := k) T).map (T.freePairedCoefficient z q a) =
      T.pairedCoefficient (k := k) z
        ((quotientFunctor (k := k) T).map q) a := by
  rw [freePairedCoefficient, pairedCoefficient,
    (quotientFunctor (k := k) T).map_comp]
  rfl

/-- The paired-coefficient construction as a linear map. -/
def pairedCoefficientLinearMap
    (z : {z : Q // z ∉ T.projective}) (x : Q) :
    (obj (k := k) T x ⟶ obj (k := k) T (T.tau z)) →ₗ[k]
      IncomingCoefficient (k := k) T x z.1 where
  toFun := T.pairedCoefficient z
  map_add' := by
    intro q r
    funext a
    simp [pairedCoefficient, Preadditive.add_comp]
  map_smul' := by
    intro c q
    funext a
    simp [pairedCoefficient, CategoryTheory.Linear.smul_comp]

@[simp]
theorem pairedCoefficientLinearMap_apply
    (z : {z : Q // z ∉ T.projective}) (x : Q)
    (q : obj (k := k) T x ⟶ obj (k := k) T (T.tau z)) :
    T.pairedCoefficientLinearMap (k := k) z x q =
      T.pairedCoefficient z q :=
  rfl

/-- The paired translation map followed by incoming summation is the mesh
relation and hence vanishes. -/
theorem incomingSumLinearMap_comp_pairedCoefficientLinearMap_eq_zero
    (z : {z : Q // z ∉ T.projective}) (x : Q) :
    (T.incomingSumLinearMap (k := k) x z.1).comp
        (T.pairedCoefficientLinearMap (k := k) z x) = 0 := by
  apply LinearMap.ext
  intro q
  change T.incomingSum (T.pairedCoefficient z q) = 0
  exact T.paired_incomingSum_eq_zero (k := k) z q

/-- Exactness at the incoming-coefficient term of the mesh-simple
presentation.  No injectivity assertion is made about the translation map. -/
theorem range_pairedCoefficientLinearMap_eq_ker_incomingSumLinearMap
    (z : {z : Q // z ∉ T.projective}) (x : Q) :
    LinearMap.range (T.pairedCoefficientLinearMap (k := k) z x) =
      LinearMap.ker (T.incomingSumLinearMap (k := k) x z.1) := by
  classical
  apply le_antisymm
  · rintro v ⟨q, rfl⟩
    rw [LinearMap.mem_ker]
    change T.incomingSum (T.pairedCoefficient z q) = 0
    exact T.paired_incomingSum_eq_zero (k := k) z q
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    let w : MagnitudeConjecture.LinearPathCategory.IncomingCoefficient
        (k := k) x z.1 :=
      fun a ↦ Classical.choose
        ((quotientFunctor (k := k) T).map_surjective (v a))
    have hw : ∀ a, (quotientFunctor (k := k) T).map (w a) = v a :=
      fun a ↦ Classical.choose_spec
        ((quotientFunctor (k := k) T).map_surjective (v a))
    have hq : (quotientFunctor (k := k) T).map
        (MagnitudeConjecture.LinearPathCategory.incomingSum w) = 0 := by
      rw [T.quotient_map_free_incomingSum]
      have hwfun :
          (fun a ↦ (quotientFunctor (k := k) T).map (w a)) = v := by
        funext a
        exact hw a
      rw [hwfun]
      exact hv
    have hIdeal :=
      (T.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k) x z.1
        (MagnitudeConjecture.LinearPathCategory.incomingSum w)).mp hq
    obtain ⟨a, g, hg, hnormal⟩ :=
      T.meshIdeal_hasNonprojectiveEndingNormalForm (k := k) z x hIdeal
    have hfree : w = T.freePairedCoefficient (k := k) z a + g := by
      apply MagnitudeConjecture.LinearPathCategory.incomingSumLinearMap_injective
        (k := k) x z.1
      rw [map_add]
      change MagnitudeConjecture.LinearPathCategory.incomingSum w =
        MagnitudeConjecture.LinearPathCategory.incomingSum
            (T.freePairedCoefficient (k := k) z a) +
          MagnitudeConjecture.LinearPathCategory.incomingSum g
      have hpaired : MagnitudeConjecture.LinearPathCategory.incomingSum
          (T.freePairedCoefficient (k := k) z a) =
          a ≫ T.meshRelation (k := k) z := by
        change MagnitudeConjecture.LinearPathCategory.incomingSum
            (fun b : MagnitudeConjecture.LinearPathCategory.IncomingArrow z.1 ↦
              a ≫ MagnitudeConjecture.LinearPathCategory.pathHom
                ((T.arrowEquiv z b.1) b.2).toPath) =
          a ≫ T.meshRelation (k := k) z
        exact T.free_paired_incomingSum_eq_comp_meshRelation (k := k) z a
      rw [hpaired]
      exact hnormal
    refine ⟨(quotientFunctor (k := k) T).map a, ?_⟩
    funext b
    have hfreeb : w b = T.freePairedCoefficient (k := k) z a b + g b := by
      simpa only [Pi.add_apply] using congrFun hfree b
    have hmap := congrArg (fun t ↦ (quotientFunctor (k := k) T).map t) hfreeb
    have hgb : (quotientFunctor (k := k) T).map (g b) = 0 :=
      (T.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k) x b.1 (g b)).mpr
        (hg b)
    rw [(quotientFunctor (k := k) T).map_add, hgb, add_zero] at hmap
    calc
      T.pairedCoefficient z ((quotientFunctor (k := k) T).map a) b =
          (quotientFunctor (k := k) T).map
            (T.freePairedCoefficient (k := k) z a b) :=
        (T.quotient_map_freePairedCoefficient_apply (k := k) z a b).symm
      _ = (quotientFunctor (k := k) T).map (w b) := hmap.symm
      _ = v b := hw b

/-- At a projective target there is no endpoint mesh relation, so the
incoming-arrow map is injective. -/
theorem incomingSumLinearMap_injective_of_projective
    (z : Q) (hz : z ∈ T.projective) (x : Q) :
    Function.Injective (T.incomingSumLinearMap (k := k) x z) := by
  classical
  apply (injective_iff_map_eq_zero (T.incomingSumLinearMap (k := k) x z)).mpr
  intro v hv
  let w : MagnitudeConjecture.LinearPathCategory.IncomingCoefficient
      (k := k) x z :=
    fun a ↦ Classical.choose
      ((quotientFunctor (k := k) T).map_surjective (v a))
  have hw : ∀ a, (quotientFunctor (k := k) T).map (w a) = v a :=
    fun a ↦ Classical.choose_spec
      ((quotientFunctor (k := k) T).map_surjective (v a))
  have hq : (quotientFunctor (k := k) T).map
      (MagnitudeConjecture.LinearPathCategory.incomingSum w) = 0 := by
    rw [T.quotient_map_free_incomingSum]
    have hwfun :
        (fun a ↦ (quotientFunctor (k := k) T).map (w a)) = v := by
      funext a
      exact hw a
    rw [hwfun]
    change T.incomingSum v = 0 at hv
    exact hv
  have hIdeal :=
    (T.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k) x z
      (MagnitudeConjecture.LinearPathCategory.incomingSum w)).mp hq
  obtain ⟨g, hg, hnormal⟩ :=
    T.meshIdeal_hasProjectiveEndingNormalForm (k := k) z hz x hIdeal
  have hfree : w = g := by
    apply MagnitudeConjecture.LinearPathCategory.incomingSumLinearMap_injective
      (k := k) x z
    exact hnormal
  funext b
  change v b = 0
  have hgb : (quotientFunctor (k := k) T).map (g b) = 0 :=
    (T.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k) x b.1 (g b)).mpr
      (hg b)
  rw [← hw b, congrFun hfree b, hgb]

/-- The natural map from the representable at the translate to the incoming
coefficient functor. -/
def translationMap (z : {z : Q // z ∉ T.projective}) :
    (CategoryTheory.linearYoneda k (T.VertexCategory (k := k))).obj
        (T.tau z) ⟶
      T.incomingCoefficientFunctor (k := k) z.1 where
  app X := ModuleCat.ofHom
    ((T.pairedCoefficientLinearMap (k := k) z X.unop).comp
      InducedCategory.homLinearEquiv.toLinearMap)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    funext a
    change (f.unop ≫ q).hom ≫
        T.incomingArrowHom (k := k)
          (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1) =
      f.unop.hom ≫
        (q.hom ≫ T.incomingArrowHom (k := k)
          (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1))
    rw [InducedCategory.comp_hom, Category.assoc]

/-- The translation map and the incoming-arrow map form a complex. -/
theorem translationMap_comp_incomingMap
    (z : {z : Q // z ∉ T.projective}) :
    T.translationMap (k := k) z ≫ T.incomingMap (k := k) z.1 = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply InducedCategory.hom_ext
  change T.incomingSum (T.pairedCoefficient z q.hom) = 0
  exact T.paired_incomingSum_eq_zero (k := k) z q.hom

/-- Objectwise exactness at the incoming-coefficient functor in the
nonprojective mesh-simple presentation. -/
theorem range_translationMap_app_eq_ker_incomingMap_app
    (z : {z : Q // z ∉ T.projective})
    (X : (T.VertexCategory (k := k))ᵒᵖ) :
    LinearMap.range ((T.translationMap (k := k) z).app X).hom =
      LinearMap.ker ((T.incomingMap (k := k) z.1).app X).hom := by
  let eτ : (X.unop ⟶ (T.tau z : T.VertexCategory (k := k))) ≃ₗ[k]
      (obj (k := k) T X.unop ⟶ obj (k := k) T (T.tau z)) :=
    InducedCategory.homLinearEquiv
  let ez : (X.unop ⟶ (z.1 : T.VertexCategory (k := k))) ≃ₗ[k]
      (obj (k := k) T X.unop ⟶ obj (k := k) T z.1) :=
    InducedCategory.homLinearEquiv
  change LinearMap.range
      ((T.pairedCoefficientLinearMap (k := k) z X.unop).comp eτ.toLinearMap) =
    LinearMap.ker
      (ez.symm.toLinearMap.comp
        (T.incomingSumLinearMap (k := k) X.unop z.1))
  ext c
  constructor
  · rintro ⟨q, rfl⟩
    rw [LinearMap.mem_ker]
    change ez.symm
      (T.incomingSum (T.pairedCoefficient z (eτ q))) = 0
    have hzero : T.incomingSum (T.pairedCoefficient z (eτ q)) = 0 :=
      T.paired_incomingSum_eq_zero (k := k) z (eτ q)
    rw [hzero, map_zero]
  · intro hc
    rw [LinearMap.mem_ker] at hc
    have hincoming : T.incomingSum c = 0 := by
      apply ez.symm.injective
      simpa using hc
    have hker : c ∈
        LinearMap.ker (T.incomingSumLinearMap (k := k) X.unop z.1) := by
      rw [LinearMap.mem_ker]
      exact hincoming
    rw [← T.range_pairedCoefficientLinearMap_eq_ker_incomingSumLinearMap
      (k := k) z X.unop] at hker
    obtain ⟨a, ha⟩ := hker
    refine ⟨eτ.symm a, ?_⟩
    change T.pairedCoefficient z (eτ (eτ.symm a)) = c
    rw [eτ.apply_symm_apply]
    exact ha

/-- At a projective vertex, every evaluated incoming map is injective. -/
theorem incomingMap_app_injective_of_projective
    (z : Q) (hz : z ∈ T.projective)
    (X : (T.VertexCategory (k := k))ᵒᵖ) :
    Function.Injective ((T.incomingMap (k := k) z).app X).hom := by
  let ez : (X.unop ⟶ (z : T.VertexCategory (k := k))) ≃ₗ[k]
      (obj (k := k) T X.unop ⟶ obj (k := k) T z) :=
    InducedCategory.homLinearEquiv
  change Function.Injective
    (ez.symm.toLinearMap.comp
      (T.incomingSumLinearMap (k := k) X.unop z))
  exact ez.symm.injective.comp
    (T.incomingSumLinearMap_injective_of_projective (k := k) z hz X.unop)

end RightMeshData

end MagnitudeConjecture.MeshCategory
