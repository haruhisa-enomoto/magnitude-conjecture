import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Exactness of finite skeletal Gabriel push-down

The map induced by orbit push-down at a fixed downstairs object is the
direct sum of the corresponding upstairs component maps.  Direct sums of
modules preserve exactness componentwise.  Detecting exactness pointwise in
the ambient functor category therefore proves that skeletal push-down is an
exact functor.

The result descends through the full subcategories of additive linear
modules and finite-dimensional finite-support modules.  In particular,
Gabriel push-down sends short exact sequences of finite-dimensional modules
to short exact sequences on the chosen orbit skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

section DirectSumExact

variable {R : Type uK} [Ring R]
variable {ι : Type w}
variable {V₁ V₂ V₃ : ι → Type uM}
variable [∀ i, AddCommGroup (V₁ i)] [∀ i, Module R (V₁ i)]
variable [∀ i, AddCommGroup (V₂ i)] [∀ i, Module R (V₂ i)]
variable [∀ i, AddCommGroup (V₃ i)] [∀ i, Module R (V₃ i)]

theorem functionExact_directSum_lmap
    (f : ∀ i, V₁ i →ₗ[R] V₂ i)
    (g : ∀ i, V₂ i →ₗ[R] V₃ i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff,
    DirectSum.ker_lmap,
    DirectSum.range_lmap]
  congr 1
  ext x
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const]
  exact forall_congr' (fun i ↦ by
    rw [(h i).linearMap_ker_eq])

end DirectSumExact

section FunctorCategoryExact

variable {J : Type u} [Category.{v} J]
variable {D : Type uM} [Category.{uK} D] [Abelian D]

theorem functorCategory_exact_of_pointwise
    (S : ShortComplex (J ⥤ D))
    (hS : ∀ X : J, (S.map ((evaluation J D).obj X)).Exact) :
    S.Exact := by
  let F : J → ((J ⥤ D) ⥤ D) := fun X ↦ (evaluation J D).obj X
  have hF : JointlyReflectIsomorphisms F := by
    constructor
    intro X Y α
    apply NatIso.isIso_of_isIso_app
  haveI : ∀ X, Functor.PreservesHomology (F X) := fun X ↦
    ((Functor.exact_tfae (F X)).out 3 2).mp
      (show PreservesFiniteLimits (F X) ∧ PreservesFiniteColimits (F X) from
        ⟨inferInstance, inferInstance⟩)
  exact (hF.exact_iff S).mpr hS

end FunctorCategoryExact

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

variable {M N : C ⥤ ModuleCat.{uM} k}
variable [M.Additive] [M.Linear k] [N.Additive] [N.Linear k]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] [N.Additive] [N.Linear k] in
theorem orbitPushdownNatTransAppLinear_eq_lmap
    (α : M ⟶ N) (X : C) :
    orbitPushdownNatTransAppLinear (A := A) α X =
      DirectSum.lmap (fun b : A ↦
        (α.app ((shiftFunctor C b).obj X)).hom) := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change orbitPushdownNatTransAppLinear (A := A) α X
      (orbitPushdownLof M X b x) =
    DirectSum.lmap (fun b : A ↦
      (α.app ((shiftFunctor C b).obj X)).hom)
      (orbitPushdownLof M X b x)
  rw [orbitPushdownNatTransAppLinear_lof]
  simp [orbitPushdownLof]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] [N.Additive] [N.Linear k] in
theorem orbitPushdownNatTransAppLinear_injective
    (α : M ⟶ N)
    (hα : ∀ X : C, Function.Injective (α.app X)) (X : C) :
    Function.Injective (orbitPushdownNatTransAppLinear (A := A) α X) := by
  rw [orbitPushdownNatTransAppLinear_eq_lmap]
  exact (DirectSum.lmap_injective _).2 (fun b ↦ hα _)

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] [N.Additive] [N.Linear k] in
theorem orbitPushdownNatTransAppLinear_surjective
    (α : M ⟶ N)
    (hα : ∀ X : C, Function.Surjective (α.app X)) (X : C) :
    Function.Surjective (orbitPushdownNatTransAppLinear (A := A) α X) := by
  rw [orbitPushdownNatTransAppLinear_eq_lmap]
  exact (DirectSum.lmap_surjective _).2 (fun b ↦ hα _)

section OrbitSkeleton

variable {G : Type w} [Group G] [MulAction G C]
variable [HasShift C (Additive G)]
variable [∀ a : Additive G, (shiftFunctor C a).Additive]
variable [∀ a : Additive G, (shiftFunctor C a).Linear k]

instance linearModuleOrbitSkeletonPushdown_preservesMonomorphisms :
    (linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G) :
      LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k).PreservesMonomorphisms where
  preserves α := by
    intro hα
    letI : Mono α := hα
    haveI : Mono ((IsLinearModule (C := C) k).ι.map α) :=
      ((IsLinearModule (C := C) k).preservesMonomorphisms_ι_of_isNormalEpiCategory).preserves α
    let V := IsLinearModule.{u, max v w, uK, max w uM}
      (C := DeckOrbitSkeleton C G) k
    let P : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k :=
      linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G)
    haveI : ∀ q, Mono ((V.ι.map
        (P.map α)).app q) := fun q ↦ by
      rw [ModuleCat.mono_iff_injective]
      change Function.Injective
        (orbitPushdownNatTransAppLinear (A := Additive G) α.hom
          (deckOrbitRepresentative
            (show MulAction.orbitRel.Quotient G C from q)))
      apply orbitPushdownNatTransAppLinear_injective
      intro X
      haveI : Mono (α.hom.app X) := by
        change Mono (((IsLinearModule (C := C) k).ι.map α).app X)
        infer_instance
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    haveI : Mono (V.ι.map
        (P.map α)) :=
      NatTrans.mono_of_mono_app _
    change Mono (P.map α)
    exact V.ι.mono_of_mono_map
      (show Mono (V.ι.map (P.map α)) from inferInstance)

instance linearModuleOrbitSkeletonPushdown_preservesEpimorphisms :
    (linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G) :
      LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k).PreservesEpimorphisms where
  preserves α := by
    intro hα
    letI : Epi α := hα
    haveI : Epi ((IsLinearModule (C := C) k).ι.map α) :=
      ((IsLinearModule (C := C) k).preservesEpimorphisms_ι_of_isNormalMonoCategory).preserves α
    let V := IsLinearModule.{u, max v w, uK, max w uM}
      (C := DeckOrbitSkeleton C G) k
    let P : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k :=
      linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G)
    haveI : ∀ q, Epi ((V.ι.map
        (P.map α)).app q) := fun q ↦ by
      rw [ModuleCat.epi_iff_surjective]
      change Function.Surjective
        (orbitPushdownNatTransAppLinear (A := Additive G) α.hom
          (deckOrbitRepresentative
            (show MulAction.orbitRel.Quotient G C from q)))
      apply orbitPushdownNatTransAppLinear_surjective
      intro X
      haveI : Epi (α.hom.app X) := by
        change Epi (((IsLinearModule (C := C) k).ι.map α).app X)
        infer_instance
      exact (ModuleCat.epi_iff_surjective _).mp inferInstance
    haveI : Epi (V.ι.map
        (P.map α)) :=
      NatTrans.epi_of_epi_app _
    change Epi (P.map α)
    exact V.ι.epi_of_epi_map
      (show Epi (V.ι.map (P.map α)) from inferInstance)

theorem linearModuleOrbitSkeletonPushdown_map_exact
    (S : ShortComplex
      (LinearModuleCategory.{u, v, uK, uM} (C := C) k))
    (hS : S.Exact) :
    (S.map
      (linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G) :
        LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
          LinearModuleCategory.{u, max v w, uK, max w uM}
            (C := DeckOrbitSkeleton C G) k)).Exact := by
  let U := IsLinearModule.{u, v, uK, uM} (C := C) k
  let V := IsLinearModule.{u, max v w, uK, max w uM}
    (C := DeckOrbitSkeleton C G) k
  let P : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k :=
    linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G)
  letI : ∀ {X Y} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) U.ι := fun {X Y} f ↦
    U.preservesKernels_ι f
  letI : ∀ {X Y} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) U.ι := fun {X Y} f ↦
    U.preservesCokernels_ι f
  letI : PreservesFiniteLimits U.ι :=
    Functor.preservesFiniteLimits_of_preservesKernels U.ι
  letI : PreservesFiniteColimits U.ι :=
    Functor.preservesFiniteColimits_of_preservesCokernels U.ι
  have hSU : (S.map U.ι).Exact := hS.map U.ι
  apply V.ι.reflects_exact_of_faithful (S.map P)
  apply functorCategory_exact_of_pointwise
  intro q
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact
    (orbitPushdownNatTransAppLinear (A := Additive G) S.f.hom
      (deckOrbitRepresentative
        (show MulAction.orbitRel.Quotient G C from q)))
    (orbitPushdownNatTransAppLinear (A := Additive G) S.g.hom
      (deckOrbitRepresentative
        (show MulAction.orbitRel.Quotient G C from q)))
  rw [orbitPushdownNatTransAppLinear_eq_lmap,
    orbitPushdownNatTransAppLinear_eq_lmap]
  apply functionExact_directSum_lmap
  intro b
  let E := (evaluation C (ModuleCat.{uM} k)).obj
    ((shiftFunctor C b).obj
      (deckOrbitRepresentative
        (show MulAction.orbitRel.Quotient G C from q)))
  letI : Functor.PreservesHomology E :=
    ((Functor.exact_tfae E).out 3 2).mp
      (show PreservesFiniteLimits E ∧ PreservesFiniteColimits E from
        ⟨inferInstance, inferInstance⟩)
  have hSE : ((S.map U.ι).map E).Exact := hSU.map E
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hSE
  exact hSE

instance linearModuleOrbitSkeletonPushdown_preservesHomology :
    (linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G) :
      LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _
    linearModuleOrbitSkeletonPushdown_map_exact

instance linearModuleOrbitSkeletonPushdown_preservesFiniteLimits :
    PreservesFiniteLimits
      (linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G) :
        LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
          LinearModuleCategory.{u, max v w, uK, max w uM}
            (C := DeckOrbitSkeleton C G) k) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance linearModuleOrbitSkeletonPushdown_preservesFiniteColimits :
    PreservesFiniteColimits
      (linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G) :
        LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
          LinearModuleCategory.{u, max v w, uK, max w uM}
            (C := DeckOrbitSkeleton C G) k) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end OrbitSkeleton

namespace CoherentDeckShift

variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_exact
    (S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hS : S.Exact) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (S.map
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))).Exact := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let U := IsFiniteDimensionalModule.{u, v, uK, uM} (C := C) k
  let V := IsFiniteDimensionalModule.{u, max v w, uK, max w uM}
    (C := DeckOrbitSkeleton C G) k
  let P : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k :=
    linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G)
  let F := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : ∀ {X Y} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) U.ι := fun {X Y} f ↦
    U.preservesKernels_ι f
  letI : ∀ {X Y} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) U.ι := fun {X Y} f ↦
    U.preservesCokernels_ι f
  letI : PreservesFiniteLimits U.ι :=
    Functor.preservesFiniteLimits_of_preservesKernels U.ι
  letI : PreservesFiniteColimits U.ι :=
    Functor.preservesFiniteColimits_of_preservesCokernels U.ι
  have hSU : (S.map U.ι).Exact := hS.map U.ι
  apply V.ι.reflects_exact_of_faithful (S.map F)
  change ((S.map U.ι).map P).Exact
  exact linearModuleOrbitSkeletonPushdown_map_exact (S.map U.ι) hSU

instance finiteDimensionalModuleOrbitSkeletonPushdown_preservesHomology :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown
      (k := k)).PreservesHomology := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact Functor.preservesHomology_of_map_exact _
    (D.finiteDimensionalModuleOrbitSkeletonPushdown_map_exact (k := k))

instance finiteDimensionalModuleOrbitSkeletonPushdown_preservesFiniteLimits :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    PreservesFiniteLimits
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

instance finiteDimensionalModuleOrbitSkeletonPushdown_preservesFiniteColimits :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    PreservesFiniteColimits
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_shortExact
    (S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hS : S.ShortExact) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (S.map
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))).ShortExact := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact hS.map_of_exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
