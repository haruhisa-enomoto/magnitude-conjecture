import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import MagnitudeConjecture.CategoryTheory.OrbitPushdownRepresentable

/-!
# Deck translations of representable modules

Inverse precomposition sends the covariant representable at `X` to the
covariant representable at the correspondingly shifted object.  Consequently,
freeness of the deck action on isomorphism classes of category objects gives
trivial deck stabilizers for finite-dimensional representables.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

/-- Freeness of an action on categorical vertices, i.e. on isomorphism
classes of objects rather than only on the underlying object type. -/
def IsFreeOnIsomorphismClasses {C G : Type*} [Category C] [Group G]
    [MulAction G C] : Prop :=
  ∀ (g : G) (X : C), Nonempty (X ≅ g • X) → g = 1

/-- Freeness on isomorphism classes restricts to every subgroup. -/
theorem IsFreeOnIsomorphismClasses.restrict
    {C G : Type*} [Category C] [Group G] [MulAction G C]
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (N : Subgroup G) :
    IsFreeOnIsomorphismClasses (C := C) (G := N) := by
  intro n X h
  apply Subtype.ext
  apply hfree (n : G) X
  simpa only [MulAction.subgroup_smul_def] using h

namespace CoherentDeckShift

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

universe u' v'

variable {E : Type u'} [Category.{v'} E]
variable [MulAction G E] [Preadditive E] [CategoryTheory.Linear k E]

/-- Restriction of a covariant representable along a linear functor. -/
noncomputable def linearCoyonedaRestrictionLinearModule
    (F : CategoryTheory.Functor C E) [F.Additive] [F.Linear k]
    (X : E) : LinearModuleCategory (C := C) k :=
  ⟨F ⋙ (linearCoyoneda k E).obj (Opposite.op X),
    inferInstance, inferInstance⟩

/-- The linear adjunction isomorphism between morphisms into an inverse shift
and morphisms out of the corresponding positive shift. -/
noncomputable def representableShiftLinearEquiv (a : Additive G) (X Y : C) :
    (X ⟶ (D.core.F (-a)).obj Y) ≃ₗ[k]
      ((D.core.F a).obj X ⟶ Y) := by
  letI := D.hasShift
  let e := (shiftEquiv C a).toAdjunction.homEquiv X Y
  exact
    { toFun := e.symm
      invFun := e
      left_inv := e.apply_symm_apply
      right_inv := e.symm_apply_apply
      map_add' := fun q r ↦ by
        change
          (D.core.F a).map (q + r) ≫
              (shiftNegShift (C := C) (X := Y) a).hom =
            (D.core.F a).map q ≫
                (shiftNegShift (C := C) (X := Y) a).hom +
              (D.core.F a).map r ≫
                (shiftNegShift (C := C) (X := Y) a).hom
        simp only [Functor.map_add, Preadditive.add_comp]
      map_smul' := fun c q ↦ by
        change
          (D.core.F a).map (c • q) ≫
              (shiftNegShift (C := C) (X := Y) a).hom =
            c • ((D.core.F a).map q ≫
              (shiftNegShift (C := C) (X := Y) a).hom)
        simp only [Functor.map_smul, CategoryTheory.Linear.smul_comp] }

set_option backward.isDefEq.respectTransparency false in
/-- Inverse precomposition of a covariant linear representable is the
representable at the positively shifted source object. -/
noncomputable def linearCoyonedaPrecompositionIso
    (a : Additive G) (X : C) :
    D.core.F (-a) ⋙
        (linearCoyoneda k C).obj (Opposite.op X) ≅
      (linearCoyoneda k C).obj
        (Opposite.op ((D.core.F a).obj X)) := by
  letI := D.hasShift
  refine NatIso.ofComponents
    (fun Y ↦ (D.representableShiftLinearEquiv (k := k) a X Y).toModuleIso)
    ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  exact (shiftEquiv C a).toAdjunction.homEquiv_naturality_right_symm q f

/-- A translated restriction of a covariant representable along a
shift-compatible functor is represented by the correspondingly translated
ambient object. -/
noncomputable def linearCoyonedaRestrictionShiftIso
    (DE : CoherentDeckShift E G)
    [∀ a : Additive G, (DE.core.F a).Additive]
    [∀ a : Additive G, (DE.core.F a).Linear k]
    (F : CategoryTheory.Functor C E)
    [F.Additive] [F.Linear k]
    (hcomm :
      letI := D.hasShift
      letI := DE.hasShift
      F.CommShift (Additive G))
    (a : Additive G) (X : E) :
    letI := linearModuleCategoryHasShift (k := k) D.core
    (linearCoyonedaRestrictionLinearModule (k := k) F X)⟦a⟧ ≅
      linearCoyonedaRestrictionLinearModule (k := k) F
        ((DE.core.F a).obj X) := by
  letI := D.hasShift
  letI := DE.hasShift
  letI : F.CommShift (Additive G) := hcomm
  letI := linearModuleCategoryHasShift (k := k) D.core
  apply ObjectProperty.isoMk
  exact linearModuleShiftUnderlyingIso (k := k) D.core
      (linearCoyonedaRestrictionLinearModule (k := k) F X) a ≪≫
    (Functor.associator (D.core.F (-a)) F
      ((linearCoyoneda k E).obj (Opposite.op X))).symm ≪≫
    Functor.isoWhiskerRight (F.commShiftIso (-a))
      ((linearCoyoneda k E).obj (Opposite.op X)) ≪≫
    Functor.associator F (DE.core.F (-a))
      ((linearCoyoneda k E).obj (Opposite.op X)) ≪≫
    Functor.isoWhiskerLeft F
      (DE.linearCoyonedaPrecompositionIso (k := k) a X)

/-- A translated covariant representable is represented by the correspondingly
translated source object. -/
noncomputable def linearCoyonedaLinearModuleShiftIso
    (a : Additive G) (X : C) :
    letI := linearModuleCategoryHasShift (k := k) D.core
    (linearCoyonedaLinearModule (k := k) X)⟦a⟧ ≅
      linearCoyonedaLinearModule (k := k) ((D.core.F a).obj X) := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  apply ObjectProperty.isoMk
  exact linearModuleShiftUnderlyingIso (k := k) D.core
      (linearCoyonedaLinearModule (k := k) X) a ≪≫
    D.linearCoyonedaPrecompositionIso (k := k) a X

/-- The representable-shift comparison restricted to finite-dimensional
modules. -/
noncomputable def finiteDimensionalLinearCoyonedaShiftIso
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (a : Additive G) (X : C) :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (finiteDimensionalLinearCoyoneda (k := k) X (hP X))⟦a⟧ ≅
      finiteDimensionalLinearCoyoneda (k := k)
        ((D.core.F a).obj X) (hP ((D.core.F a).obj X)) := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  apply ObjectProperty.isoMk
  exact D.finiteDimensionalModuleShiftUnderlyingIso (k := k)
      (finiteDimensionalLinearCoyoneda (k := k) X (hP X)) a ≪≫
    D.linearCoyonedaLinearModuleShiftIso (k := k) a X

/-- Freeness on isomorphism classes of representing objects implies trivial
deck stabilizers for finite-dimensional representables. -/
theorem finiteDimensionalLinearCoyoneda_trivialStabilizer
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (X : C) (a : Additive G) :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    Nonempty
        (finiteDimensionalLinearCoyoneda (k := k) X (hP X) ≅
          (finiteDimensionalLinearCoyoneda (k := k) X (hP X))⟦a⟧) →
      a = 0 := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  rintro ⟨e⟩
  let eFinite := e ≪≫
    D.finiteDimensionalLinearCoyonedaShiftIso (k := k) hP a X
  let eLinear := (IsFiniteDimensionalModule (C := C) k).ι.mapIso eFinite
  let eFunctor := (IsLinearModule (C := C) k).ι.mapIso eLinear
  let eRepresenting := (linearCoyoneda k C).preimageIso eFunctor
  have hinv : a.toMul⁻¹ = 1 :=
    hfree a.toMul⁻¹ X ⟨eRepresenting.unop.symm ≪≫
      D.objIso a.toMul X⟩
  exact toMul_eq_one.mp (inv_eq_one.mp hinv)

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
