import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation
import MagnitudeConjecture.CategoryTheory.MeshSimpleTranslation
import MagnitudeConjecture.CategoryTheory.ModuleFunctorExact
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite mesh-simple presentations

The objectwise mesh calculations assemble into categorical exact sequences of
contravariant mesh modules.  When the mesh representables are finite-
dimensional, the simple, the incoming coefficient module, and all displayed
maps restrict to the existing finite-dimensional linear-module category.

The use of the opposite vertex category is deliberate: a contravariant mesh
module is a covariant linear module on the opposite category, so this file
reuses the package's established covariant module API rather than introducing
a parallel convention.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.MeshCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

noncomputable instance vertexCategoryFintype :
    Fintype (T.VertexCategory (k := k)) := by
  change Fintype Q
  infer_instance

noncomputable instance oppositeVertexCategoryFintype :
    Fintype ((T.VertexCategory (k := k))ᵒᵖ) :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

instance simpleFunctor_additive (z : Q) :
    (T.simpleFunctor (k := k) z).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro q
    induction q using Submodule.Quotient.induction_on with
    | _ q =>
      change T.simpleValueProjection (k := k) Y.unop z
          ((f.unop.hom + g.unop.hom) ≫ q) =
        T.simpleValueProjection (k := k) Y.unop z (f.unop.hom ≫ q) +
          T.simpleValueProjection (k := k) Y.unop z (g.unop.hom ≫ q)
      rw [Preadditive.add_comp, map_add]

instance simpleFunctor_linear (z : Q) :
    (T.simpleFunctor (k := k) z).Linear k where
  map_smul := by
    intro X Y f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro q
    induction q using Submodule.Quotient.induction_on with
    | _ q =>
      change T.simpleValueProjection (k := k) Y.unop z
          ((r • f.unop.hom) ≫ q) =
        r • T.simpleValueProjection (k := k) Y.unop z
          (f.unop.hom ≫ q)
      rw [CategoryTheory.Linear.smul_comp, map_smul]

instance incomingCoefficientFunctor_additive (z : Q) :
    (T.incomingCoefficientFunctor (k := k) z).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (f.unop.hom + g.unop.hom) ≫ c a =
      f.unop.hom ≫ c a + g.unop.hom ≫ c a
    rw [Preadditive.add_comp]

instance incomingCoefficientFunctor_linear (z : Q) :
    (T.incomingCoefficientFunctor (k := k) z).Linear k where
  map_smul := by
    intro X Y f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (r • f.unop.hom) ≫ c a = r • (f.unop.hom ≫ c a)
    rw [CategoryTheory.Linear.smul_comp]

instance contravariantRepresentableFunctor_linear (y : Q) :
    ((CategoryTheory.linearYoneda k
      (T.VertexCategory (k := k))).obj y).Linear k where
  map_smul := by
    intro X Y f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change (r • f).unop ≫ q = r • (f.unop ≫ q)
    rw [opposite_unop_smul, CategoryTheory.Linear.smul_comp]

/-- Insert one contravariant representable as the coefficient belonging to
an incoming arrow. -/
def incomingSummandInclusion (z : Q) (a : IncomingArrow z) :
    (CategoryTheory.linearYoneda k
        (T.VertexCategory (k := k))).obj a.1 ⟶
      T.incomingCoefficientFunctor (k := k) z := by
  classical
  exact
    { app := fun X ↦ ModuleCat.ofHom
        { toFun := fun q b ↦ if h : a = b then h ▸ q.hom else 0
          map_add' := by
            intro q r
            funext b
            by_cases h : a = b
            · subst b
              simp only [dif_pos, Pi.add_apply]
              exact (InducedCategory.homLinearEquiv
                (R := k)).map_add q r
            · simp [h]
          map_smul' := by
            intro c q
            funext b
            by_cases h : a = b
            · subst b
              simp only [dif_pos, Pi.smul_apply, RingHom.id_apply]
              exact (InducedCategory.homLinearEquiv
                (R := k)).map_smul c q
            · simp [h] }
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        funext b
        by_cases h : a = b
        · subst b
          change (if h' : a = a then h' ▸ (f.unop ≫ q).hom else 0) =
            f.unop.hom ≫ (if h' : a = a then h' ▸ q.hom else 0)
          simp [InducedCategory.comp_hom]
        · change (if h' : a = b then h' ▸ (f.unop ≫ q).hom else 0) =
            f.unop.hom ≫ (if h' : a = b then h' ▸ q.hom else 0)
          simp [h] }

/-- Project an incoming coefficient family to the contravariant
representable indexed by one incoming arrow. -/
def incomingSummandProjection (z : Q) (a : IncomingArrow z) :
    T.incomingCoefficientFunctor (k := k) z ⟶
      (CategoryTheory.linearYoneda k
        (T.VertexCategory (k := k))).obj a.1 where
  app X := ModuleCat.ofHom
    { toFun := fun c ↦ InducedCategory.homMk (c a)
      map_add' := by
        intro c d
        apply InducedCategory.hom_ext
        rfl
      map_smul' := by
        intro r c
        apply InducedCategory.hom_ext
        rfl }
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply InducedCategory.hom_ext
    rfl

@[simp]
theorem incomingSummandInclusion_comp_projection_self
    (z : Q) (a : IncomingArrow z) :
    T.incomingSummandInclusion (k := k) z a ≫
        T.incomingSummandProjection (k := k) z a =
      𝟙 ((CategoryTheory.linearYoneda k
        (T.VertexCategory (k := k))).obj a.1) := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply InducedCategory.hom_ext
  change (InducedCategory.homMk
    (if h : a = a then h ▸ q.hom else 0)).hom = q.hom
  simp

theorem incomingSummandInclusion_comp_projection_eq_zero
    (z : Q) {a b : IncomingArrow z} (h : a ≠ b) :
    T.incomingSummandInclusion (k := k) z a ≫
        T.incomingSummandProjection (k := k) z b = 0 := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply InducedCategory.hom_ext
  change (InducedCategory.homMk
      (if h' : a = b then h' ▸ q.hom else 0)).hom =
    (0 : Opposite.unop X ⟶ b.1).hom
  rw [dif_neg h]
  exact (InducedCategory.homLinearEquiv (R := k)).map_zero.symm

/-- Summing the coordinate projection-inclusion endomorphisms recovers an
incoming coefficient family. -/
theorem sum_incomingSummandProjection_comp_inclusion (z : Q) :
    (∑ a : IncomingArrow z,
      T.incomingSummandProjection (k := k) z a ≫
        T.incomingSummandInclusion (k := k) z a) =
      𝟙 (T.incomingCoefficientFunctor (k := k) z) := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext b
  have happ :
      (∑ a : IncomingArrow z,
        T.incomingSummandProjection (k := k) z a ≫
          T.incomingSummandInclusion (k := k) z a).app X =
        ∑ a : IncomingArrow z,
          (T.incomingSummandProjection (k := k) z a ≫
            T.incomingSummandInclusion (k := k) z a).app X := by
    exact NatTrans.app_sum (Finset.univ : Finset (IncomingArrow z)) X
      (fun a ↦ T.incomingSummandProjection (k := k) z a ≫
        T.incomingSummandInclusion (k := k) z a)
  rw [happ]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply,
    NatTrans.comp_app, ModuleCat.comp_apply, NatTrans.id_app,
    ModuleCat.id_apply]
  let u := fun a : IncomingArrow z ↦
    ((T.incomingSummandInclusion (k := k) z a).app X).hom
      (((T.incomingSummandProjection (k := k) z a).app X).hom c)
  change (∑ a : IncomingArrow z, u a) b = c b
  have hterm (a : IncomingArrow z) :
      u a b = if h : a = b then h ▸ c a else 0 := by
    rfl
  have hsum (s : Finset (IncomingArrow z)) :
      (∑ a ∈ s, u a) b = ∑ a ∈ s, u a b := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change u a b + (∑ x ∈ s, u x) b =
        u a b + ∑ x ∈ s, u x b
      rw [ih]
  rw [hsum Finset.univ]
  rw [Finset.sum_congr rfl (fun a _ ↦ hterm a)]
  simp

/-- Restricting the incoming-arrow map to one representable summand is the
Yoneda image of that incoming arrow. -/
@[simp]
theorem incomingSummandInclusion_comp_incomingMap
    (z : Q) (a : IncomingArrow z) :
    T.incomingSummandInclusion (k := k) z a ≫
        T.incomingMap (k := k) z =
      (CategoryTheory.linearYoneda k
        (T.VertexCategory (k := k))).map
          (InducedCategory.homMk (T.incomingArrowHom (k := k) a)) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply InducedCategory.hom_ext
  classical
  change T.incomingSum
      (fun b : IncomingArrow z ↦ if h : a = b then h ▸ q.hom else 0) =
    q.hom ≫ T.incomingArrowHom (k := k) a
  rw [← T.incomingSum_single (a₀ := a) q.hom]
  congr 1
  funext b
  by_cases h : a = b
  · subst b
    simp [singleIncomingCoefficient]
  · simp [singleIncomingCoefficient, h]

/-- The translation differential is the sum of the Yoneda maps represented
by the polarized partners, followed by the corresponding summand
inclusions. -/
theorem translationMap_eq_sum_paired_incoming
    (z : {z : Q // z ∉ T.projective}) :
    T.translationMap (k := k) z =
      ∑ a : IncomingArrow z.1,
        (CategoryTheory.linearYoneda k
          (T.VertexCategory (k := k))).map
            (InducedCategory.homMk
              (T.incomingArrowHom (k := k)
                (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1))) ≫
          T.incomingSummandInclusion (k := k) z.1 a := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  funext b
  have happ :
      ((∑ a : IncomingArrow z.1,
          (CategoryTheory.linearYoneda k
            (T.VertexCategory (k := k))).map
              (InducedCategory.homMk
                (T.incomingArrowHom (k := k)
                  (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1))) ≫
            T.incomingSummandInclusion (k := k) z.1 a).app X) =
        ∑ a : IncomingArrow z.1,
          (((CategoryTheory.linearYoneda k
            (T.VertexCategory (k := k))).map
              (InducedCategory.homMk
                (T.incomingArrowHom (k := k)
                  (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1))) ≫
            T.incomingSummandInclusion (k := k) z.1 a).app X) := by
    exact NatTrans.app_sum (Finset.univ : Finset (IncomingArrow z.1)) X _
  rw [happ]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, NatTrans.comp_app,
    ModuleCat.comp_apply]
  change (T.pairedCoefficientLinearMap (k := k) z X.unop
      (InducedCategory.homLinearEquiv q)) b = _
  rw [T.pairedCoefficientLinearMap_apply]
  let qraw := InducedCategory.homLinearEquiv (R := k) q
  let mapped := fun a : IncomingArrow z.1 ↦
    (((CategoryTheory.linearYoneda k
      (T.VertexCategory (k := k))).map
        (InducedCategory.homMk
          (T.incomingArrowHom (k := k)
            (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1)))).app X).hom q
  let term := fun a : IncomingArrow z.1 ↦
    ((T.incomingSummandInclusion (k := k) z.1 a).app X).hom (mapped a)
  change T.pairedCoefficient (k := k) z qraw b =
    (∑ a : IncomingArrow z.1, term a) b
  have hsum : (∑ a : IncomingArrow z.1, term a) b =
      ∑ a : IncomingArrow z.1, (term a) b := by
    induction (Finset.univ : Finset (IncomingArrow z.1)) using Finset.induction_on with
    | empty => rfl
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change term a b + (∑ x ∈ s, term x) b =
        term a b + ∑ x ∈ s, term x b
      rw [ih]
  rw [hsum]
  have hterm (a : IncomingArrow z.1) : (term a) b =
      if h : a = b then h ▸
        (qraw ≫ T.incomingArrowHom (k := k)
          (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1))
      else 0 := by
    rfl
  rw [Finset.sum_congr rfl (fun a _ ↦ hterm a)]
  change qraw ≫ T.incomingArrowHom (k := k)
      (⟨T.tau z, T.arrowEquiv z b.1 b.2⟩ : IncomingArrow b.1) =
    (∑ a : IncomingArrow z.1,
      if h : a = b then h ▸
        (qraw ≫ T.incomingArrowHom (k := k)
          (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1))
      else 0)
  simp

/-- The literal contravariant mesh representable used by the mesh maps,
bundled as a covariant linear module on the opposite vertex category. -/
def contravariantRepresentableLinearModule (y : Q) :
    LinearModuleCategory (C := (T.VertexCategory (k := k))ᵒᵖ) k :=
  ⟨(CategoryTheory.linearYoneda k
      (T.VertexCategory (k := k))).obj y,
    inferInstance, inferInstance⟩

/-- The mesh simple as a covariant linear module on the opposite vertex
category. -/
def simpleLinearModule (z : Q) :
    LinearModuleCategory (C := (T.VertexCategory (k := k))ᵒᵖ) k :=
  ⟨T.simpleFunctor (k := k) z, inferInstance, inferInstance⟩

/-- The incoming coefficient functor as a covariant linear module on the
opposite vertex category. -/
def incomingCoefficientLinearModule (z : Q) :
    LinearModuleCategory (C := (T.VertexCategory (k := k))ᵒᵖ) k :=
  ⟨T.incomingCoefficientFunctor (k := k) z, inferInstance, inferInstance⟩

/-- Every mesh simple is finite-dimensional and supported only at its named
vertex.  This does not require finite-dimensional mesh Hom spaces. -/
theorem simpleLinearModule_isFiniteDimensional (z : Q) :
    IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k
      (simpleLinearModule (k := k) T z) := by
  constructor
  · intro X
    change FiniteDimensional k (T.simpleValue (k := k) X.unop z)
    by_cases hX : X.unop = z
    · subst z
      exact (T.simpleValueSelfLinearEquiv (k := k) X.unop).finiteDimensional
    · letI : Subsingleton (T.simpleValue (k := k) X.unop z) :=
        T.simpleValue_subsingleton_of_ne (k := k) hX
      infer_instance
  · change (moduleSupport k (T.simpleFunctor (k := k) z)).Finite
    exact Set.toFinite _

/-- The mesh simple bundled in the finite-dimensional linear-module
category. -/
def simpleFiniteModule (z : Q) :
    FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k :=
  ⟨simpleLinearModule (k := k) T z,
    T.simpleLinearModule_isFiniteDimensional (k := k) z⟩

/-- The mesh simple supported at a vertex is a simple object of the
finite-dimensional module category. -/
instance simpleFiniteModule_simple (z : Q) :
    Simple (T.simpleFiniteModule (k := k) z) := by
  let S := T.simpleFiniteModule (k := k) z
  have hS_id_ne : (𝟙 S : S ⟶ S) ≠ 0 := by
    intro hzero
    let e := T.simpleValueSelfLinearEquiv (k := k) z
    have hz := congrArg
      (fun q : S ⟶ S ↦ (q.hom.hom.app (Opposite.op z)).hom) hzero
    have hzv := DFunLike.congr_fun hz (e 1)
    change e 1 = 0 at hzv
    have hezero : e 1 = 0 := hzv
    rw [← map_zero e] at hezero
    exact one_ne_zero (e.injective hezero)
  refine ⟨fun {N} f _ ↦ ?_⟩
  constructor
  · intro _ hfzero
    apply hS_id_ne
    apply (cancel_epi f).1
    rw [Category.comp_id, hfzero, zero_comp]
  · intro hf
    let J := (IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
    let I := (IsLinearModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
    have hfz : ((I.map (J.map f)).app (Opposite.op z)).hom ≠ 0 := by
      intro hfz
      apply hf
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext X
      rcases X with ⟨X⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      by_cases hX : X = z
      · subst z
        exact DFunLike.congr_fun hfz x
      · letI : Subsingleton
            ((T.simpleFiniteModule (k := k) z).obj.obj.obj
              (Opposite.op X)) := by
          change Subsingleton (T.simpleValue (k := k) X z)
          exact T.simpleValue_subsingleton_of_ne (k := k) hX
        exact Subsingleton.elim _ _
    haveI hepiApp (X : (T.VertexCategory (k := k))ᵒᵖ) :
        Epi ((I.map (J.map f)).app X) := by
      rw [ModuleCat.epi_iff_surjective]
      rcases X with ⟨X⟩
      by_cases hX : X = z
      · subst z
        apply surjective_of_nonzero_of_finrank_eq_one (K := k)
        · change Module.finrank k (T.simpleValue (k := k) X X) = 1
          simpa using
            (T.simpleValueSelfLinearEquiv (k := k) X).finrank_eq.symm
        · exact hfz
      · letI : Subsingleton
            ((I.obj (J.obj (T.simpleFiniteModule (k := k) z))).obj
              (Opposite.op X)) := by
          change Subsingleton (T.simpleValue (k := k) X z)
          exact T.simpleValue_subsingleton_of_ne (k := k) hX
        intro y
        exact ⟨0, Subsingleton.elim _ _⟩
    haveI : Epi (I.map (J.map f)) := NatTrans.epi_of_epi_app _
    haveI : Epi (J.map f) := I.epi_of_epi_map inferInstance
    haveI : Epi f := J.epi_of_epi_map inferInstance
    exact isIso_of_mono_of_epi f

/-- Finite-dimensionality of all contravariant vertex representables,
expressed in the package's covariant-on-the-opposite convention. -/
abbrev FiniteContravariantRepresentables :=
  ∀ X : (T.VertexCategory (k := k))ᵒᵖ,
    IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k
      (linearCoyonedaLinearModule (k := k) X)

/-- Evaluation of the covariant representable on the opposite vertex
category is the expected contravariant raw mesh Hom space. -/
def contravariantRepresentableValueLinearEquiv
    (X : (T.VertexCategory (k := k))ᵒᵖ) (y : Q) :
    (linearCoyonedaLinearModule
        (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
        (Opposite.op y)).obj.obj X ≃ₗ[k]
      (obj (k := k) T X.unop ⟶ obj (k := k) T y) where
  toFun f := f.unop.hom
  invFun f := (InducedCategory.homMk f).op
  left_inv f := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The opposite-category covariant representable and the literal
contravariant mesh representable are naturally isomorphic. -/
def contravariantRepresentableRawIso (y : Q) :
    (CategoryTheory.linearCoyoneda k
        ((T.VertexCategory (k := k))ᵒᵖ)).obj
          (Opposite.op (Opposite.op y)) ≅
      (CategoryTheory.linearYoneda k
        (T.VertexCategory (k := k))).obj y := by
  refine NatIso.ofComponents
    (fun X ↦ (oppositeHomLinearEquiv (k := k)
      (C := T.VertexCategory (k := k)) (Opposite.op y) X).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  rfl

/-- Linear-module form of the identification between the package's standard
opposite-category representable and the literal mesh representable. -/
def contravariantRepresentableLinearIso (y : Q) :
    linearCoyonedaLinearModule
        (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
        (Opposite.op y) ≅
      T.contravariantRepresentableLinearModule (k := k) y :=
  ObjectProperty.isoMk _
    (T.contravariantRepresentableRawIso (k := k) y)

/-- A literal contravariant mesh representable is finite-dimensional whenever
the corresponding opposite-category covariant representable is. -/
theorem contravariantRepresentableLinearModule_isFiniteDimensional
    (hP : T.FiniteContravariantRepresentables (k := k)) (y : Q) :
    IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k
      (T.contravariantRepresentableLinearModule (k := k) y) :=
  (IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k).prop_of_iso
    (T.contravariantRepresentableLinearIso (k := k) y)
    (hP (Opposite.op y))

/-- The literal contravariant mesh representable bundled in the
finite-dimensional linear-module category. -/
def contravariantRepresentableFiniteModule
    (hP : T.FiniteContravariantRepresentables (k := k)) (y : Q) :
    FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k :=
  ⟨T.contravariantRepresentableLinearModule (k := k) y,
    T.contravariantRepresentableLinearModule_isFiniteDimensional
      (k := k) hP y⟩

/-- Finite-module form of the identification with the package's standard
opposite-category projective representable. -/
def contravariantRepresentableFiniteIso
    (hP : T.FiniteContravariantRepresentables (k := k)) (y : Q) :
    finiteDimensionalLinearCoyoneda
        (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
        (Opposite.op y) (hP (Opposite.op y)) ≅
      T.contravariantRepresentableFiniteModule (k := k) hP y :=
  ObjectProperty.isoMk _
    (T.contravariantRepresentableLinearIso (k := k) y)

instance contravariantRepresentableFiniteModule_projective
    (hP : T.FiniteContravariantRepresentables (k := k)) (y : Q) :
    Projective (T.contravariantRepresentableFiniteModule (k := k) hP y) :=
  Projective.of_iso
    (T.contravariantRepresentableFiniteIso (k := k) hP y)
    (finiteDimensionalLinearCoyoneda_projective
      (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
      (Opposite.op y) (hP (Opposite.op y)))

/-- Under finite-dimensionality of the mesh representables, the incoming
coefficient module is finite-dimensional. -/
theorem incomingCoefficientLinearModule_isFiniteDimensional
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k
      (incomingCoefficientLinearModule (k := k) T z) := by
  constructor
  · intro X
    change FiniteDimensional k (IncomingCoefficient (k := k) T X.unop z)
    letI (a : IncomingArrow z) : FiniteDimensional k
        (obj (k := k) T X.unop ⟶ obj (k := k) T a.1) := by
      letI : FiniteDimensional k
          ((linearCoyonedaLinearModule
            (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
            (Opposite.op a.1)).obj.obj X) :=
        (hP (Opposite.op a.1)).1 X
      exact (T.contravariantRepresentableValueLinearEquiv
        (k := k) X a.1).finiteDimensional
    infer_instance
  · change (moduleSupport k
        (T.incomingCoefficientFunctor (k := k) z)).Finite
    exact Set.toFinite _

/-- The incoming coefficient module bundled in the finite-dimensional
linear-module category. -/
def incomingCoefficientFiniteModule
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k :=
  ⟨incomingCoefficientLinearModule (k := k) T z,
    T.incomingCoefficientLinearModule_isFiniteDimensional (k := k) hP z⟩

/-- Finite-dimensional lift of one coordinate inclusion into the incoming
coefficient module. -/
def incomingSummandInclusionFinite
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : Q) (a : IncomingArrow z) :
    T.contravariantRepresentableFiniteModule (k := k) hP a.1 ⟶
      T.incomingCoefficientFiniteModule (k := k) hP z :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (T.incomingSummandInclusion (k := k) z a))

/-- Finite-dimensional lift of one coordinate projection from the incoming
coefficient module. -/
def incomingSummandProjectionFinite
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : Q) (a : IncomingArrow z) :
    T.incomingCoefficientFiniteModule (k := k) hP z ⟶
      T.contravariantRepresentableFiniteModule (k := k) hP a.1 :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (T.incomingSummandProjection (k := k) z a))

@[simp]
theorem incomingSummandInclusionFinite_comp_projection_self
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : Q) (a : IncomingArrow z) :
    T.incomingSummandInclusionFinite (k := k) hP z a ≫
        T.incomingSummandProjectionFinite (k := k) hP z a =
      𝟙 (T.contravariantRepresentableFiniteModule (k := k) hP a.1) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact T.incomingSummandInclusion_comp_projection_self (k := k) z a

theorem incomingSummandInclusionFinite_comp_projection_eq_zero
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : Q) {a b : IncomingArrow z} (h : a ≠ b) :
    T.incomingSummandInclusionFinite (k := k) hP z a ≫
        T.incomingSummandProjectionFinite (k := k) hP z b = 0 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact T.incomingSummandInclusion_comp_projection_eq_zero
    (k := k) z h

theorem sum_incomingSummandProjectionFinite_comp_inclusion
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    (∑ a : IncomingArrow z,
      T.incomingSummandProjectionFinite (k := k) hP z a ≫
        T.incomingSummandInclusionFinite (k := k) hP z a) =
      𝟙 (T.incomingCoefficientFiniteModule (k := k) hP z) := by
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let f := fun a : IncomingArrow z ↦
    T.incomingSummandProjectionFinite (k := k) hP z a ≫
      T.incomingSummandInclusionFinite (k := k) hP z a
  apply J.map_injective
  apply I.map_injective
  have hJ : J.map (∑ a, f a) = ∑ a, J.map (f a) := by
    exact J.map_sum f (Finset.univ : Finset (IncomingArrow z))
  have hI : I.map (∑ a, J.map (f a)) =
      ∑ a, I.map (J.map (f a)) := by
    exact I.map_sum (fun a ↦ J.map (f a))
      (Finset.univ : Finset (IncomingArrow z))
  rw [hJ, hI]
  change (∑ a : IncomingArrow z,
    T.incomingSummandProjection (k := k) z a ≫
      T.incomingSummandInclusion (k := k) z a) =
    𝟙 (T.incomingCoefficientFunctor (k := k) z)
  exact T.sum_incomingSummandProjection_comp_inclusion (k := k) z

/-- A fixed finite enumeration of the arrows into a vertex. -/
def incomingArrowEquivFin (z : Q) :
    IncomingArrow z ≃ Fin (Fintype.card (IncomingArrow z)) :=
  Fintype.equivFin _

/-- The incoming coefficient module is the finite biproduct of the
contravariant representables indexed by arrows into the vertex. -/
def incomingRepresentableBiproductIso
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    (⨁ fun i : Fin (Fintype.card (IncomingArrow z)) ↦
      T.contravariantRepresentableFiniteModule (k := k) hP
        ((incomingArrowEquivFin z).symm i).1) ≅
      T.incomingCoefficientFiniteModule (k := k) hP z where
  hom := biproduct.desc (fun i ↦
    T.incomingSummandInclusionFinite (k := k) hP z
      ((incomingArrowEquivFin z).symm i))
  inv := biproduct.lift (fun i ↦
    T.incomingSummandProjectionFinite (k := k) hP z
      ((incomingArrowEquivFin z).symm i))
  hom_inv_id := by
    let e := incomingArrowEquivFin z
    let P := fun i : Fin (Fintype.card (IncomingArrow z)) ↦
      T.contravariantRepresentableFiniteModule (k := k) hP (e.symm i).1
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, biproduct.ι_desc_assoc,
      biproduct.lift_π, Category.comp_id]
    by_cases h : i = j
    · subst j
      rw [T.incomingSummandInclusionFinite_comp_projection_self
        (k := k) hP z (e.symm i)]
      exact (biproduct.ι_π_self P i).symm
    · have h' : e.symm i ≠ e.symm j := fun q ↦ h (e.symm.injective q)
      rw [T.incomingSummandInclusionFinite_comp_projection_eq_zero
        (k := k) hP z h']
      exact (biproduct.ι_π_ne P h).symm
  inv_hom_id := by
    let e := incomingArrowEquivFin z
    let g := fun a : IncomingArrow z ↦
      T.incomingSummandProjectionFinite (k := k) hP z a ≫
        T.incomingSummandInclusionFinite (k := k) hP z a
    calc
      (biproduct.lift (fun i ↦
          T.incomingSummandProjectionFinite (k := k) hP z (e.symm i)) ≫
        biproduct.desc (fun i ↦
          T.incomingSummandInclusionFinite (k := k) hP z (e.symm i))) =
          ∑ i : Fin (Fintype.card (IncomingArrow z)), g (e.symm i) := by
        simpa [g] using (biproduct.lift_desc
          (f := fun i : Fin (Fintype.card (IncomingArrow z)) ↦
            T.contravariantRepresentableFiniteModule
              (k := k) hP (e.symm i).1)
          (g := fun i ↦ T.incomingSummandProjectionFinite
            (k := k) hP z (e.symm i))
          (h := fun i ↦ T.incomingSummandInclusionFinite
            (k := k) hP z (e.symm i)))
      _ = ∑ a : IncomingArrow z, g a := e.symm.sum_comp g
      _ = 𝟙 (T.incomingCoefficientFiniteModule (k := k) hP z) :=
        T.sum_incomingSummandProjectionFinite_comp_inclusion
          (k := k) hP z

instance incomingRepresentableBiproduct_projective
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    Projective (⨁ fun i : Fin (Fintype.card (IncomingArrow z)) ↦
      T.contravariantRepresentableFiniteModule (k := k) hP
        ((incomingArrowEquivFin z).symm i).1) := by
  let P := fun i : Fin (Fintype.card (IncomingArrow z)) ↦
    T.contravariantRepresentableFiniteModule (k := k) hP
      ((incomingArrowEquivFin z).symm i).1
  constructor
  intro E X f q hq
  refine ⟨biproduct.desc (fun i ↦
    Projective.factorThru (biproduct.ι P i ≫ f) q), ?_⟩
  apply biproduct.hom_ext'
  intro i
  simp [P]

instance incomingCoefficientFiniteModule_projective
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    Projective (T.incomingCoefficientFiniteModule (k := k) hP z) :=
  Projective.of_iso
    (T.incomingRepresentableBiproductIso (k := k) hP z)
    (T.incomingRepresentableBiproduct_projective (k := k) hP z)

/-- Finite-dimensional lift of the projection from the vertex
representable to its mesh simple. -/
def simpleProjectionFinite
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    T.contravariantRepresentableFiniteModule (k := k) hP z ⟶
      T.simpleFiniteModule (k := k) z :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (T.simpleProjection (k := k) z))

/-- Finite-dimensional lift of the incoming-arrow map. -/
def incomingMapFinite
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    T.incomingCoefficientFiniteModule (k := k) hP z ⟶
      T.contravariantRepresentableFiniteModule (k := k) hP z :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (T.incomingMap (k := k) z))

/-- Finite-dimensional lift of the paired translation map. -/
def translationMapFinite
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : {z : Q // z ∉ T.projective}) :
    T.contravariantRepresentableFiniteModule (k := k) hP (T.tau z) ⟶
      T.incomingCoefficientFiniteModule (k := k) hP z.1 :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (T.translationMap (k := k) z))

instance simpleProjectionFinite_epi
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    Epi (T.simpleProjectionFinite (k := k) hP z) := by
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  haveI : Epi (I.map (J.map
      (T.simpleProjectionFinite (k := k) hP z))) := by
    change Epi (T.simpleProjection (k := k) z)
    infer_instance
  haveI : Epi (J.map
      (T.simpleProjectionFinite (k := k) hP z)) :=
    I.epi_of_epi_map inferInstance
  exact J.epi_of_epi_map inferInstance

/-- The standard opposite-category projective representable maps onto the
mesh simple through its identification with the literal mesh
representable. -/
def simpleStandardAugmentation
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    finiteDimensionalLinearCoyoneda
        (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
        (Opposite.op z) (hP (Opposite.op z)) ⟶
      T.simpleFiniteModule (k := k) z :=
  (T.contravariantRepresentableFiniteIso (k := k) hP z).hom ≫
    T.simpleProjectionFinite (k := k) hP z

instance simpleStandardAugmentation_epi
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    Epi (T.simpleStandardAugmentation (k := k) hP z) := by
  dsimp [simpleStandardAugmentation]
  infer_instance

/-- The canonical one-generator finite representable presentation of a mesh
simple. -/
def simpleFiniteRepresentablePresentation
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    FiniteRepresentablePresentation hP
      (T.simpleFiniteModule (k := k) z) where
  n := 1
  X := fun _ ↦ Opposite.op z
  f := biproduct.desc (fun _ ↦
    T.simpleStandardAugmentation (k := k) hP z)
  epi := by
    let R := finiteDimensionalLinearCoyoneda
      (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
      (Opposite.op z) (hP (Opposite.op z))
    let e := T.simpleStandardAugmentation (k := k) hP z
    change Epi (biproduct.desc (fun _ : Fin 1 ↦ e))
    haveI : Epi e := by
      dsimp [e]
      infer_instance
    exact epi_of_epi_fac
      (f := biproduct.ι (fun _ : Fin 1 ↦ R) (0 : Fin 1))
      (g := biproduct.desc (fun _ : Fin 1 ↦ e))
      (h := e) (by simp)

/-- The positive-tail mesh presentation in the ambient functor category. -/
def simplePositiveShortComplex (z : Q) :
    ShortComplex
      ((T.VertexCategory (k := k))ᵒᵖ ⥤ ModuleCat k) :=
  ShortComplex.mk (T.incomingMap (k := k) z)
    (T.simpleProjection (k := k) z)
    (T.incomingMap_comp_simpleProjection (k := k) z)

/-- The paired-translation part of a nonprojective mesh-simple
presentation in the ambient functor category. -/
def simpleTranslationShortComplex
    (z : {z : Q // z ∉ T.projective}) :
    ShortComplex
      ((T.VertexCategory (k := k))ᵒᵖ ⥤ ModuleCat k) :=
  ShortComplex.mk (T.translationMap (k := k) z)
    (T.incomingMap (k := k) z.1)
    (T.translationMap_comp_incomingMap (k := k) z)

/-- The positive-tail mesh presentation is categorically exact. -/
theorem simplePositiveShortComplex_exact (z : Q) :
    (T.simplePositiveShortComplex (k := k) z).Exact := by
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  exact T.range_incomingMap_app_eq_ker_simpleProjection_app (k := k) z X

/-- The paired-translation mesh presentation is categorically exact at its
middle term. -/
theorem simpleTranslationShortComplex_exact
    (z : {z : Q // z ∉ T.projective}) :
    (T.simpleTranslationShortComplex (k := k) z).Exact := by
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  exact T.range_translationMap_app_eq_ker_incomingMap_app (k := k) z X

/-- The positive-tail mesh presentation inside the finite-dimensional
linear-module category. -/
def simplePositiveFiniteShortComplex
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    ShortComplex (FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
  ShortComplex.mk (T.incomingMapFinite (k := k) hP z)
    (T.simpleProjectionFinite (k := k) hP z) (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact T.incomingMap_comp_simpleProjection (k := k) z)

/-- The paired-translation part of the mesh-simple presentation inside the
finite-dimensional linear-module category. -/
def simpleTranslationFiniteShortComplex
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : {z : Q // z ∉ T.projective}) :
    ShortComplex (FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
  ShortComplex.mk (T.translationMapFinite (k := k) hP z)
    (T.incomingMapFinite (k := k) hP z.1) (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact T.translationMap_comp_incomingMap (k := k) z)

/-- The finite-dimensional positive-tail mesh presentation is exact. -/
theorem simplePositiveFiniteShortComplex_exact
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    (T.simplePositiveFiniteShortComplex (k := k) hP z).Exact := by
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  apply J.reflects_exact_of_faithful
    (T.simplePositiveFiniteShortComplex (k := k) hP z)
  apply I.reflects_exact_of_faithful
    ((T.simplePositiveFiniteShortComplex (k := k) hP z).map J)
  exact T.simplePositiveShortComplex_exact (k := k) z

/-- The finite-dimensional paired-translation mesh presentation is exact at
its middle term. -/
theorem simpleTranslationFiniteShortComplex_exact
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : {z : Q // z ∉ T.projective}) :
    (T.simpleTranslationFiniteShortComplex (k := k) hP z).Exact := by
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  apply J.reflects_exact_of_faithful
    (T.simpleTranslationFiniteShortComplex (k := k) hP z)
  apply I.reflects_exact_of_faithful
    ((T.simpleTranslationFiniteShortComplex (k := k) hP z).map J)
  exact T.simpleTranslationShortComplex_exact (k := k) z

/-- The positive-tail presentation with its projective middle term written
in the package's standard opposite-category representable convention. -/
def simpleStandardPositiveShortComplex
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    ShortComplex (FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
  ShortComplex.mk
    (T.incomingMapFinite (k := k) hP z ≫
      (T.contravariantRepresentableFiniteIso (k := k) hP z).inv)
    (T.simpleStandardAugmentation (k := k) hP z) (by
      simp only [simpleStandardAugmentation, Category.assoc,
        Iso.inv_hom_id_assoc]
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact T.incomingMap_comp_simpleProjection (k := k) z)

/-- Replacing the literal mesh representable by the standard
opposite-category representable gives an isomorphic short complex. -/
def simplePositiveFiniteStandardIso
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    T.simplePositiveFiniteShortComplex (k := k) hP z ≅
      T.simpleStandardPositiveShortComplex (k := k) hP z := by
  refine ShortComplex.isoMk
    (S₁ := T.simplePositiveFiniteShortComplex (k := k) hP z)
    (S₂ := T.simpleStandardPositiveShortComplex (k := k) hP z)
    (Iso.refl _)
    (T.contravariantRepresentableFiniteIso (k := k) hP z).symm
    (Iso.refl _) ?_ ?_
  · simp [simplePositiveFiniteShortComplex,
      simpleStandardPositiveShortComplex]
  · simp [simplePositiveFiniteShortComplex,
      simpleStandardPositiveShortComplex, simpleStandardAugmentation]

/-- The standard-representable positive-tail presentation is exact. -/
theorem simpleStandardPositiveShortComplex_exact
    (hP : T.FiniteContravariantRepresentables (k := k)) (z : Q) :
    (T.simpleStandardPositiveShortComplex (k := k) hP z).Exact :=
  (ShortComplex.exact_iff_of_iso
    (T.simplePositiveFiniteStandardIso (k := k) hP z)).mp
      (T.simplePositiveFiniteShortComplex_exact (k := k) hP z)

end RightMeshData

end MagnitudeConjecture.MeshCategory
