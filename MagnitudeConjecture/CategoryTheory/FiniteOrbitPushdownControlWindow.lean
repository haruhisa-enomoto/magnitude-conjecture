import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleControlWindow
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownWindow
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownShift
import MagnitudeConjecture.CategoryTheory.AlmostSplitFiniteCoreFunctor
import MagnitudeConjecture.CategoryTheory.IrreducibleFiniteCoreFunctor
import MagnitudeConjecture.CategoryTheory.ShiftOrbitControlWindow

/-!
# Local closure for finite Gabriel push-down

Assume the finite-dimensional push-down is essentially surjective, the
essential-surjectivity form of Gabriel's density theorem.  A nonzero map to
or from a downstairs module then lifts through the Gabriel Hom equivalence to
a nonzero shifted Hom upstairs.  One Hom-interaction enlargement therefore
contains a translated lift of the external object.  Push-down's translation
invariance supplies the essential-image witness inside that window.

This proves the local factorization and endpoint closure used to transport
irreducible and almost-split maps.  It deliberately leaves Gabriel's density
theorem itself as the remaining covering-theoretic input.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The exact density conclusion for finite-dimensional Gabriel push-down. -/
structure FiniteOrbitPushdownDensity : Prop where
  essSurj : letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ((finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, w, uK, uM}
        D (k := k)) :
      FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k).EssSurj

/-- If an indecomposable downstairs module is nonzero at the orbit of `y`,
density has a translated indecomposable lift in the finite fiber seed at
`y`.  The translated lift has the same push-down isomorphism class. -/
theorem finiteOrbitPushdown_exists_seed_lift_of_nontrivial
    {k₀ : Type v} [Field k₀] [CategoryTheory.Linear k₀ C]
    (D₀ : CoherentDeckShift C G)
    [∀ a : Additive G, (D₀.core.F a).Additive]
    [∀ a : Additive G, (D₀.core.F a).Linear k₀]
    (hlocal : IsLocallyRepresentationFinite (k := k₀) (C := C))
    (hP : FiniteOrbitPushdownDensity.{u, v, w, v, v} (k := k₀) D₀)
    (y : C) :
    letI := D₀.hasShift
    letI := D₀.additiveShift
    letI := D₀.linearShift (k := k₀)
    letI := isLinearModule_stableUnderShift (k := k₀) D₀.core
    letI := linearModuleCategoryHasShift (k := k₀) D₀.core
    letI := linearModuleCategoryAdditiveShift (R := k₀) D₀.core
    letI := linearModuleCategoryLinearShift (R := k₀) D₀.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, v, max w v}
        (C := ShiftOrbitCategory C (Additive G)) k₀) (Additive G)
    let P := D₀.finiteDimensionalModuleOrbitSkeletonPushdown (k := k₀)
    ∀ (Y : FiniteDimensionalModuleCategory.{u, max v w, v, max w v}
        (C := DeckOrbitSkeleton C G) k₀),
      Indecomposable Y →
      Nontrivial (Y.obj.obj.obj
        (Quotient.mk'' y : MulAction.orbitRel.Quotient G C)) →
      ∃ X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k₀,
        Indecomposable X ∧ X ∈ (finiteFiberControlSeed hlocal y).isoClosure ∧
          Nontrivial (X.obj.obj.obj y) ∧ Nonempty (P.obj X ≅ Y) := by
  dsimp
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k₀)
  letI := isLinearModule_stableUnderShift (k := k₀) D₀.core
  letI := linearModuleCategoryHasShift (k := k₀) D₀.core
  letI := linearModuleCategoryAdditiveShift (R := k₀) D₀.core
  letI := linearModuleCategoryLinearShift (R := k₀) D₀.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, v, max w v}
      (C := ShiftOrbitCategory C (Additive G)) k₀) (Additive G)
  let P := D₀.finiteDimensionalModuleOrbitSkeletonPushdown (k := k₀)
  haveI : P.Faithful :=
    D₀.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k₀)
  intro Y hY hYq
  obtain ⟨V, ⟨e⟩⟩ := hP.essSurj.mem_essImage Y
  have hPV : Indecomposable (P.obj V) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).2 hY
  have hV : Indecomposable V :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P V hPV
  let q : DeckOrbitSkeleton C G :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient G C)
  let J := (IsFiniteDimensionalModule.{u, max v w, v, max w v}
    (C := DeckOrbitSkeleton C G) k₀).ι
  let K := (IsLinearModule.{u, max v w, v, max w v}
    (C := DeckOrbitSkeleton C G) k₀).ι
  let eq := (K.mapIso (J.mapIso e)).app q
  have hPVq : Nontrivial ((P.obj V).obj.obj.obj q) :=
    eq.toLinearEquiv.toEquiv.nontrivial_congr.mpr hYq
  have hnall : ¬ ∀ b : Additive G,
      IsZero (V.obj.obj.obj ((shiftFunctor C b).obj
        (deckOrbitRepresentative (C := C) (G := G) q))) := by
    intro hall
    have hzero : IsZero ((P.obj V).obj.obj.obj q) :=
      (D₀.orbitSkeletonPushdown_obj_isZero_iff (k := k₀) V q).2 hall
    letI : Subsingleton ((P.obj V).obj.obj.obj q) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero
    exact not_nontrivial _ hPVq
  push Not at hnall
  obtain ⟨b, hb⟩ := hnall
  have hbNontrivial : Nontrivial
      (V.obj.obj.obj ((shiftFunctor C b).obj
        (deckOrbitRepresentative (C := C) (G := G) q))) := by
    exact not_subsingleton_iff_nontrivial.mp fun hsub ↦
      hb (ModuleCat.isZero_iff_subsingleton.mpr hsub)
  have hqrep :
      (Quotient.mk'' (deckOrbitRepresentative (C := C) (G := G) q) :
        MulAction.orbitRel.Quotient G C) = Quotient.mk'' y :=
    deckOrbitRepresentative_mk (C := C) (G := G) q
  have horbit : deckOrbitRepresentative (C := C) (G := G) q ∈
      MulAction.orbit G y :=
    MulAction.orbitRel_apply.mp (Quotient.exact hqrep)
  obtain ⟨n, hn⟩ := horbit
  change n • y = deckOrbitRepresentative (C := C) (G := G) q at hn
  let g : G := b.toMul⁻¹ * n
  have hVgy : Nontrivial (V.obj.obj.obj (g • y)) := by
    have hsupp := (D₀.nontrivial_shift_value_iff (k := k₀) V b
      (deckOrbitRepresentative (C := C) (G := G) q)).1 hbNontrivial
    change Nontrivial (V.obj.obj.obj (b.toMul⁻¹ •
      deckOrbitRepresentative (C := C) (G := G) q)) at hsupp
    simpa only [g, ← hn, mul_smul] using hsupp
  let a : Additive G := Additive.ofMul g
  let V' : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k₀ := V⟦a⟧
  have hV' : Indecomposable V' :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k₀) a)
      V).2 hV
  have hV'y : Nontrivial (V'.obj.obj.obj y) := by
    exact (D₀.finiteDimensionalModuleShiftEvaluationIso
      (k := k₀) V g y).toLinearEquiv.toEquiv.nontrivial_congr.mpr hVgy
  have hseed : V' ∈ (finiteFiberControlSeed hlocal y).isoClosure :=
    mem_finiteFiberControlSeed_isoClosure hlocal y hV' hV'y
  refine ⟨V', hV', hseed, hV'y, ⟨?_⟩⟩
  exact (D₀.finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
    (k := k₀) V a) ≪≫ e

/-- The local essential image need only contain indecomposable objects which
support nonzero maps from and to the two endpoints.  Density supplies an
upstairs lift; faithfulness of global push-down reflects its downstairs
indecomposability, and a shift of that lift lies in the prescribed
indecomposable Hom-neighborhood. -/
theorem finiteOrbitPushdownWindow_locallyIndecomposableBifactorClosed
    (U W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hUW : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) U ⊆ W)
    (hP : FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D)
    (X Y : CoveringSeparation.WindowCategory W) (hX : X.1 ∈ U) :
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
    MagnitudeConjecture.IsLocallyIndecomposableBifactorClosed
      (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W)
        X Y := by
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
  let P : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k :=
    finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, w, uK, uM}
      D (k := k)
  letI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k)
  have hP' : P.EssSurj := hP.essSurj
  intro M hM g hg h hh
  obtain ⟨V, ⟨e⟩⟩ := hP'.mem_essImage M
  have hPV : Indecomposable (P.obj V) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).2 hM
  have hV : Indecomposable V :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P V hPV
  let E := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) X.1 V
  let q : ShiftOrbitHom (Additive G) X.1.obj V.obj := E.symm (g ≫ e.inv)
  have hge : g ≫ e.inv ≠ 0 := by
    intro hzero
    apply hg
    apply (cancel_mono e.inv).1
    simpa using hzero
  have hq : q ≠ 0 := by
    intro hzero
    apply hge
    calc
      g ≫ e.inv = E q := (E.apply_symm_apply (g ≫ e.inv)).symm
      _ = E 0 := congrArg E hzero
      _ = 0 := map_zero E
  obtain ⟨a, ha⟩ := exists_shiftOrbitHom_component_ne_zero hq
  let V' : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k := V⟦a⟧
  have hV' : Indecomposable V' :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) a)
      V).mpr hV
  let es := D.finiteDimensionalModuleShiftUnderlyingIso (k := k) V a
  let f : X.1 ⟶ V' := ObjectProperty.homMk (q a ≫ es.inv)
  have hf : f ≠ 0 := by
    intro hzero
    apply ha
    apply (cancel_mono es.inv).1
    simpa [f] using congrArg (fun t ↦ t.hom) hzero
  have hnontrivial : Nontrivial (X.1 ⟶ V') := ⟨⟨f, 0, hf⟩⟩
  have hV'W : V' ∈ W :=
    hUW ⟨X.1, hX, hV', Or.inr (Or.inl hnontrivial)⟩
  refine ⟨⟨V', hV'W⟩, ⟨?_⟩⟩
  exact (D.finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
    (k := k) V a) ≪≫ e

/-- Density puts every indecomposable source relevant to right
almost-splitness into a prescribed indecomposable Hom-neighborhood. -/
theorem finiteOrbitPushdownWindow_locallyIndecomposableRightObjectClosed
    (U W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hUW : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) U ⊆ W)
    (hP : FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D)
    (Y : CoveringSeparation.WindowCategory W) (hY : Y.1 ∈ U) :
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
    MagnitudeConjecture.IsLocallyIndecomposableRightObjectClosedAt
      (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W) Y := by
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
  let P : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k :=
    finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, w, uK, uM}
      D (k := k)
  letI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k)
  have hP' : P.EssSurj := hP.essSurj
  intro M hM g hg _
  obtain ⟨V, ⟨e⟩⟩ := hP'.mem_essImage M
  have hPV : Indecomposable (P.obj V) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).2 hM
  have hV : Indecomposable V :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P V hPV
  let E := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) V Y.1
  let q : ShiftOrbitHom (Additive G) V.obj Y.1.obj := E.symm (e.hom ≫ g)
  have heg : e.hom ≫ g ≠ 0 := by
    intro hzero
    apply hg
    apply (cancel_epi e.hom).1
    simpa using hzero
  have hq : q ≠ 0 := by
    intro hzero
    apply heg
    calc
      e.hom ≫ g = E q := (E.apply_symm_apply (e.hom ≫ g)).symm
      _ = E 0 := congrArg E hzero
      _ = 0 := map_zero E
  obtain ⟨a, ha⟩ := exists_shiftOrbitHom_component_ne_zero hq
  let V' : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k := V⟦-a⟧
  have hV' : Indecomposable V' :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) (-a))
      V).mpr hV
  let es := D.finiteDimensionalModuleShiftUnderlyingIso (k := k) V (-a)
  let f : V' ⟶ Y.1 := ObjectProperty.homMk
    (es.hom ≫ (shiftFunctor
      (LinearModuleCategory.{u, v, uK, uM} (C := C) k) (-a)).map (q a) ≫
        (shiftShiftNeg Y.1.obj a).hom)
  have hf : f ≠ 0 := by
    intro hzero
    apply ha
    let T := shiftFunctor
      (LinearModuleCategory.{u, v, uK, uM} (C := C) k) (-a)
    have hright : T.map (q a) ≫ (shiftShiftNeg Y.1.obj a).hom = 0 := by
      simpa [f, T, Category.assoc] using congrArg (fun t ↦ t.hom) hzero
    have hmap : T.map (q a) = 0 := by
      apply (cancel_mono (shiftShiftNeg Y.1.obj a).hom).1
      simpa using hright
    apply T.map_injective
    rw [T.map_zero]
    exact hmap
  have hnontrivial : Nontrivial (V' ⟶ Y.1) := ⟨⟨f, 0, hf⟩⟩
  have hV'W : V' ∈ W :=
    hUW ⟨Y.1, hY, hV', Or.inr (Or.inr hnontrivial)⟩
  refine ⟨⟨V', hV'W⟩, ⟨?_⟩⟩
  exact (D.finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
    (k := k) V (-a)) ≪≫ e

/-- A nonzero map from a represented source to an indecomposable downstairs
target lifts to a nonzero shifted Hom upstairs.  If one Hom-interaction
enlargement carries `U` into `W`, a translated lift of the target lies in
`W` and has the prescribed push-down isomorphism class. -/
theorem finiteOrbitPushdownWindow_exists_target_lift_of_ne_zero
    (U W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hUW : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) U ⊆ W)
    (hP : FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D)
    (X : CoveringSeparation.WindowCategory W) (hX : X.1 ∈ U) :
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
    let P := D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
      (k := k) W
    ∀ (Y : FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k),
      Indecomposable Y → ∀ (f : P.obj X ⟶ Y), f ≠ 0 →
        ∃ V : CoveringSeparation.WindowCategory W,
          Nonempty (P.obj V ≅ Y) := by
  dsimp
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
  let P : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k :=
    finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, w, uK, uM}
      D (k := k)
  haveI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k)
  intro Y hY f hf
  obtain ⟨V, ⟨e⟩⟩ := hP.essSurj.mem_essImage Y
  have hPV : Indecomposable (P.obj V) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).2 hY
  have hV : Indecomposable V :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P V hPV
  let E := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) X.1 V
  let q : ShiftOrbitHom (Additive G) X.1.obj V.obj := E.symm (f ≫ e.inv)
  have hfe : f ≫ e.inv ≠ 0 := by
    intro hzero
    apply hf
    apply (cancel_mono e.inv).1
    simpa using hzero
  have hq : q ≠ 0 := by
    intro hzero
    apply hfe
    calc
      f ≫ e.inv = E q := (E.apply_symm_apply (f ≫ e.inv)).symm
      _ = E 0 := congrArg E hzero
      _ = 0 := map_zero E
  obtain ⟨a, ha⟩ := exists_shiftOrbitHom_component_ne_zero hq
  let V' : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k := V⟦a⟧
  have hV' : Indecomposable V' :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) a)
      V).mpr hV
  let es := D.finiteDimensionalModuleShiftUnderlyingIso (k := k) V a
  let g : X.1 ⟶ V' := ObjectProperty.homMk (q a ≫ es.inv)
  have hg : g ≠ 0 := by
    intro hzero
    apply ha
    apply (cancel_mono es.inv).1
    simpa [g] using congrArg (fun t ↦ t.hom) hzero
  have hnontrivial : Nontrivial (X.1 ⟶ V') := ⟨⟨g, 0, hg⟩⟩
  have hV'W : V' ∈ W :=
    hUW ⟨X.1, hX, hV', Or.inr (Or.inl hnontrivial)⟩
  refine ⟨⟨V', hV'W⟩, ⟨?_⟩⟩
  exact (D.finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
    (k := k) V a) ≪≫ e

/-- The dual density argument puts every indecomposable target relevant to
left almost-splitness into the prescribed Hom-neighborhood. -/
theorem finiteOrbitPushdownWindow_locallyIndecomposableLeftObjectClosed
    (U W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hUW : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) U ⊆ W)
    (hP : FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D)
    (X : CoveringSeparation.WindowCategory W) (hX : X.1 ∈ U) :
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
    MagnitudeConjecture.IsLocallyIndecomposableLeftObjectClosedAt
      (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W) X := by
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
  intro M hM g hg _
  exact D.finiteOrbitPushdownWindow_exists_target_lift_of_ne_zero
    U W hUW hP X hX M hM g hg

/-- Density, shifted-Hom orthogonality, and an indecomposable Hom-neighborhood
identify irreducibility before and after finite skeletal push-down.  An
arbitrary decomposable intermediate object is replaced internally by the
finite biproduct of summands on which both factor maps are nonzero. -/
theorem
    isIrreducibleMorphism_finiteOrbitPushdownWindowMap_iff_of_density_finiteCore
    (U W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    [HasFiniteBiproducts (CoveringSeparation.WindowCategory W)]
    (hUW : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) U ⊆ W)
    (hP : FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D)
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (hX : X.1 ∈ U) :
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
    (IsIrreducibleMorphism
        ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
          (k := k) W).map f) ↔
      IsIrreducibleMorphism f) := by
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
  let F := D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W
  letI : F.Additive := by
    dsimp [F, finiteDimensionalModuleOrbitSkeletonPushdownWindow]
    infer_instance
  letI : F.Full :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_full
      (k := k) W horthogonal
  letI : F.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_faithful (k := k) W
  exact MagnitudeConjecture.isIrreducibleMorphism_map_iff_of_finiteIndecomposableCore
    F finiteDimensionalModule_finiteIndecomposableDecomposition
      (D.finiteOrbitPushdownWindow_locallyIndecomposableBifactorClosed
        U W hUW hP X Y hX)

/-- Density, shifted-Hom orthogonality, and an indecomposable Hom-neighborhood
transport right almost-split maps.  Arbitrary decomposable test objects are
reduced internally to their nonzero indecomposable components. -/
theorem rightAlmostSplit_finiteOrbitPushdownWindowMap_of_density_finiteCore
    (U W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hUW : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) U ⊆ W)
    (hP : FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D)
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit f) (hY : Y.1 ∈ U) :
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
    IsRightAlmostSplit
      ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
        (k := k) W).map f) := by
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
  let F := D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W
  letI : F.Additive := by
    dsimp [F, finiteDimensionalModuleOrbitSkeletonPushdownWindow]
    infer_instance
  letI : F.Full :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_full
      (k := k) W horthogonal
  letI : F.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_faithful (k := k) W
  exact
    MagnitudeConjecture.rightAlmostSplit_map_of_full_faithful_of_finiteIndecomposableCore
      F finiteDimensionalModule_finiteIndecomposableDecomposition hf
        (D.finiteOrbitPushdownWindow_locallyIndecomposableRightObjectClosed
          U W hUW hP Y hY)

/-- The dual finite-core statement transports left almost-split maps. -/
theorem leftAlmostSplit_finiteOrbitPushdownWindowMap_of_density_finiteCore
    (U W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hUW : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) U ⊆ W)
    (hP : FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D)
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f) (hX : X.1 ∈ U) :
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
    IsLeftAlmostSplit
      ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
        (k := k) W).map f) := by
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
  let F := D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W
  letI : F.Additive := by
    dsimp [F, finiteDimensionalModuleOrbitSkeletonPushdownWindow]
    infer_instance
  letI : F.Full :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_full
      (k := k) W horthogonal
  letI : F.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_faithful (k := k) W
  exact
    MagnitudeConjecture.leftAlmostSplit_map_of_full_faithful_of_finiteIndecomposableCore
      F finiteDimensionalModule_finiteIndecomposableDecomposition hf
        (D.finiteOrbitPushdownWindow_locallyIndecomposableLeftObjectClosed
          U W hUW hP X hX)

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
