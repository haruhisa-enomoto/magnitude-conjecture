import MagnitudeConjecture.CategoryTheory.OrbitPushdownHomEquiv
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Restriction from the nonskeletal orbit category to its chosen deck-orbit
skeleton, on Homs between push-down modules. -/
noncomputable def linearModuleOrbitSkeletonRestrictionLinear
    (M N : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ((linearModuleOrbitPushdown
          (k := k) (C := C) (A := Additive G)).obj M ⟶
        (linearModuleOrbitPushdown
          (k := k) (C := C) (A := Additive G)).obj N) →ₗ[k]
      ((linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G)).obj M ⟶
        (linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G)).obj N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact
    { toFun := fun α ↦ ObjectProperty.homMk
        (Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C) (G := G)) α.hom)
      map_add' := by
        intro α β
        apply ObjectProperty.hom_ext
        rfl
      map_smul' := by
        intro r α
        apply ObjectProperty.hom_ext
        rfl }

set_option backward.isDefEq.respectTransparency false in
theorem linearModuleOrbitSkeletonRestrictionLinear_bijective
    (M N : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Bijective
      (linearModuleOrbitSkeletonRestrictionLinear (k := k) D M N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := deckOrbitRepresentativeFunctor (C := C) (G := G)
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := D.deckOrbitRepresentativeFunctor_essSurj }
  let W := (Functor.whiskeringLeft
    (DeckOrbitSkeleton C G)
    (ShiftOrbitCategory C (Additive G))
    (ModuleCat.{max w uM} k)).obj F
  let hW := Functor.FullyFaithful.ofFullyFaithful W
  constructor
  · intro α β h
    apply ObjectProperty.hom_ext
    apply hW.map_injective
    have hh := congrArg (fun q ↦ q.hom) h
    exact hh
  · intro β
    refine ⟨ObjectProperty.homMk (hW.preimage β.hom), ?_⟩
    apply ObjectProperty.hom_ext
    exact hW.map_preimage β.hom

/-- Restriction along the representative equivalence is a linear equivalence
on Homs between push-down modules. -/
noncomputable def linearModuleOrbitSkeletonRestrictionLinearEquiv
    (M N : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ((linearModuleOrbitPushdown
          (k := k) (C := C) (A := Additive G)).obj M ⟶
        (linearModuleOrbitPushdown
          (k := k) (C := C) (A := Additive G)).obj N) ≃ₗ[k]
      ((linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G)).obj M ⟶
        (linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G)).obj N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact LinearEquiv.ofBijective
    (linearModuleOrbitSkeletonRestrictionLinear (k := k) D M N)
    (linearModuleOrbitSkeletonRestrictionLinear_bijective (k := k) D M N)

@[simp]
theorem linearModuleOrbitSkeletonRestrictionLinearEquiv_apply
    (M N : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ (α :
        (linearModuleOrbitPushdown
            (k := k) (C := C) (A := Additive G)).obj M ⟶
          (linearModuleOrbitPushdown
            (k := k) (C := C) (A := Additive G)).obj N),
      linearModuleOrbitSkeletonRestrictionLinearEquiv (k := k) D M N α =
        ObjectProperty.homMk
          (Functor.whiskerLeft
            (deckOrbitRepresentativeFunctor (C := C) (G := G)) α.hom) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  intro α
  rfl

/-- Gabriel's Hom formula after restricting the base to the chosen deck-orbit
skeleton. -/
noncomputable def linearModuleOrbitSkeletonPushdownHomLinearEquiv
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ShiftOrbitHom (Additive G) M.obj N ≃ₗ[k]
      ((linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G)).obj M.obj ⟶
        (linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G)).obj N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  exact
    (linearModuleOrbitPushdownHomLinearEquiv D.core M N).trans
      (linearModuleOrbitSkeletonRestrictionLinearEquiv (k := k) D M.obj N)

@[simp]
theorem linearModuleOrbitSkeletonPushdownHomLinearEquiv_apply
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ (f : ShiftOrbitHom (Additive G) M.obj N),
      D.linearModuleOrbitSkeletonPushdownHomLinearEquiv (k := k) M N f =
        linearModuleOrbitSkeletonRestrictionLinear (k := k) D M.obj N
          (linearModuleOrbitPushdownSynthesisLinear D.core M.obj N f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro f
  rfl

variable [IsCancelSMul G C]

/-- Manuscript-facing Gabriel Hom formula for the literal finite-dimensional
push-down on one chosen representative of each deck orbit. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ShiftOrbitHom (Additive G) M.obj N.obj ≃ₗ[k]
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  exact
    (D.linearModuleOrbitSkeletonPushdownHomLinearEquiv (k := k) M N.obj).trans
      (InducedCategory.homLinearEquiv (R := k)
        (F := fun X : FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k ↦ X.1)
        (X := P.obj M) (Y := P.obj N)).symm

@[simp]
theorem finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_apply_hom
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ (f : ShiftOrbitHom (Additive G) M.obj N.obj),
      (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
        (k := k) M N f).hom =
          D.linearModuleOrbitSkeletonPushdownHomLinearEquiv (k := k) M N.obj f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro f
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The finite-dimensional skeletal Gabriel Hom equivalence respects
shift-orbit convolution. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
    (M N Z : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ (f : ShiftOrbitHom (Additive G) M.obj N.obj)
      (g : ShiftOrbitHom (Additive G) N.obj Z.obj),
      D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
          (k := k) M N f ≫
        D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
          (k := k) N Z g =
        D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
          (k := k) M Z (shiftOrbitCompHom f g) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro f g
  apply ObjectProperty.hom_ext
  change
    (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
        (k := k) M N f).hom ≫
      (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
        (k := k) N Z g).hom =
    (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
        (k := k) M Z (shiftOrbitCompHom f g)).hom
  rw [finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_apply_hom,
    finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_apply_hom,
    finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_apply_hom]
  apply ObjectProperty.hom_ext
  rw [linearModuleOrbitSkeletonPushdownHomLinearEquiv_apply,
    linearModuleOrbitSkeletonPushdownHomLinearEquiv_apply,
    linearModuleOrbitSkeletonPushdownHomLinearEquiv_apply]
  exact congrArg (fun α ↦
    Functor.whiskerLeft
      (deckOrbitRepresentativeFunctor (C := C) (G := G)) α.hom)
    (linearModuleOrbitPushdownSynthesisLinear_comp
      D.core M.obj N.obj Z.obj f g)

set_option backward.isDefEq.respectTransparency false in
/-- The manuscript-facing Hom equivalence sends the degree-zero inclusion of
an ordinary finite-dimensional module map to the existing finite push-down
functor map. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ (f : M ⟶ N),
      D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
          (k := k) M N
          (shiftOrbitOf M.obj N.obj 0
            (shiftHomZero (A := Additive G) f.hom)) =
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro f
  apply ObjectProperty.hom_ext
  rw [finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_apply_hom,
    linearModuleOrbitSkeletonPushdownHomLinearEquiv_apply,
    linearModuleOrbitPushdownSynthesisLinear_zero]
  rfl

/-- Gabriel's Hom decomposition for one pair of finite-dimensional upstairs
modules and their literal skeletal push-downs. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownHomDecomposition
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    OrbitHomDecomposition (k := k)
      (H := fun g : Multiplicative (Additive G) ↦
        multiplicativeShiftHom
          (C := LinearModuleCategory.{u, v, uK, uM} (C := C) k)
          (A := Additive G) M.obj N.obj g)
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  classical
  let E := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M N
  exact
    { homEquiv := E.symm.trans
        (multiplicativeShiftHomDirectSumEquiv
          (A := Additive G) M.obj N.obj)
      lift := E.toLinearMap.comp (shiftOrbitLof (k := k) M.obj N.obj 0)
      homEquiv_lift := by
        intro f
        change multiplicativeShiftHomDirectSumEquiv
            (k := k) (A := Additive G) M.obj N.obj
              (E.symm (E (shiftOrbitLof (k := k) M.obj N.obj 0 f))) =
          identityLof (k := k)
            (H := fun g : Multiplicative (Additive G) ↦
              multiplicativeShiftHom
                (C := LinearModuleCategory.{u, v, uK, uM} (C := C) k)
                (A := Additive G) M.obj N.obj g) f
        rw [E.symm_apply_apply]
        exact DirectSum.lequivCongrLeft_lof k
          (e := Multiplicative.ofAdd) (i := (0 : Additive G))
          (k := (1 : Multiplicative (Additive G))) rfl f f rfl }

/-- The finite-dimensional skeletal push-down satisfies the functor-level
Gabriel orbit Hom interface. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownOrbitHomDecomposition :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    FunctorOrbitHomDecomposition (k := k)
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))
      (fun M N g ↦ multiplicativeShiftHom
        (C := LinearModuleCategory.{u, v, uK, uM} (C := C) k)
        (A := Additive G) M.obj N.obj g) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  exact
    { sourceEquiv := fun M N ↦
        (InducedCategory.homLinearEquiv (R := k)).trans
          (shiftHomZeroLinearEquiv (A := Additive G) M.obj N.obj)
      homDecomposition :=
        D.finiteDimensionalModuleOrbitSkeletonPushdownHomDecomposition (k := k)
      map_compat := by
        intro M N f
        exact D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
          (k := k) M N f }

/-- Finite-dimensional skeletal Gabriel push-down is faithful, without any
translate-orthogonality hypothesis. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_faithful :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).Faithful := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdownOrbitHomDecomposition
      (k := k)).faithful

/-- Faithfulness of finite push-down transported across an explicit equality
of shift instances. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_faithful
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift) :
    letI := H
    letI := hadd
    letI := hlinear
    (D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
      (k := k) H hadd hlinear hH).Faithful := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  change (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).Faithful
  exact D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k)

/-- If an upstairs indecomposable module has no maps to any of its nontrivial
shifts, then its literal finite skeletal push-down is indecomposable.  This is
the separated-window form of Gabriel's indecomposability argument and does not
use density. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_selfShiftHomOrthogonal
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (∀ a : Additive G, a ≠ 0 →
      Subsingleton (ShiftHom M.obj M.obj a)) →
      Indecomposable
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hM
  intro orthogonal
  apply
    (D.finiteDimensionalModuleOrbitSkeletonPushdownOrbitHomDecomposition
      (k := k)).indecomposable_map_of_end_orthogonal M
  intro g hg
  apply orthogonal g.toAdd
  intro hzero
  apply hg
  apply Multiplicative.toAdd.injective
  simpa using hzero

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
