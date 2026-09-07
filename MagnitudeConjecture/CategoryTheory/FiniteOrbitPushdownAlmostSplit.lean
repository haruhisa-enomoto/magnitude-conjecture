import MagnitudeConjecture.CategoryTheory.AlmostSplitComparison
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownExact
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownHomEquiv
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownIndecomposable
import MagnitudeConjecture.CategoryTheory.ShiftOrbitFactorization
import MagnitudeConjecture.CategoryTheory.ShiftOrbitLocalAlgebra

/-!
# Almost-split factorization under finite skeletal push-down

This file formalizes the componentwise adjunction/Hom-formula step in
Gabriel's proof that push-down preserves Auslander--Reiten sequences.  A
downstairs endomorphism is decomposed into finitely many homogeneous maps to
deck translates.  Once its identity component is known not to be split
monic, trivial deck stabilizer gives the same conclusion in every nonidentity
degree.  The upstairs left almost-split map then factors all components, and
finite-support convolution assembles the required downstairs factorization.

The identity-component assertion is proved by comparing the residue maps of
the upstairs and downstairs finite-dimensional local endomorphism algebras.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- A homogeneous map between the underlying linear modules, regarded as a
map to the corresponding finite-dimensional shifted module. -/
noncomputable def finiteDimensionalShiftHom
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ShiftHom M.obj N.obj a → (M ⟶ N⟦a⟧) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro q
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let e := D.finiteDimensionalModuleShiftUnderlyingIso (k := k) N a
  exact J.preimage (q ≫ e.inv)

set_option backward.isDefEq.respectTransparency false in
theorem finiteDimensionalShiftHom_map
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ q : ShiftHom M.obj N.obj a,
      (IsFiniteDimensionalModule (C := C) k).ι.map
          (finiteDimensionalShiftHom (k := k) D M N a q) =
        q ≫ (D.finiteDimensionalModuleShiftUnderlyingIso
          (k := k) N a).inv := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro q
  exact (IsFiniteDimensionalModule (C := C) k).ι.map_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- Passing a homogeneous map into the finite shifted category and then back
to the underlying shifted linear module recovers the original map. -/
theorem finiteDimensionalShiftHom_roundtrip
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ q : ShiftHom M.obj N.obj a,
      (IsFiniteDimensionalModule (C := C) k).ι.map
          (finiteDimensionalShiftHom (k := k) D M N a q) ≫
        (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) N a).hom = q := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro q
  rw [finiteDimensionalShiftHom_map]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Trivial deck stabilizer passes from a finite-dimensional module to its
underlying linear module. -/
theorem finiteDimensionalModule_trivial_linear_stabilizer
    (L : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (∀ a : Additive G, Nonempty (L ≅ L⟦a⟧) → a = 0) →
      ∀ a : Additive G, Nonempty (L.obj ≅ L.obj⟦a⟧) → a = 0 := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro htrivial a
  rintro ⟨e⟩
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let eshift := D.finiteDimensionalModuleShiftUnderlyingIso (k := k) L a
  exact htrivial a ⟨J.preimageIso (e ≪≫ eshift.symm)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finite-dimensional factorization of one homogeneous component gives
the corresponding singleton factorization in the shift-orbit category. -/
theorem shiftOrbitComponent_factor
    (L E : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : Additive G) (f : L ⟶ E) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ q : ShiftHom L.obj L.obj a,
    ∀ c : E ⟶ L⟦a⟧,
    f ≫ c = finiteDimensionalShiftHom (k := k) D L L a q →
      shiftOrbitCompHom
          (shiftOrbitOf L.obj E.obj 0
            (shiftHomZero (A := Additive G) f.hom))
          (shiftOrbitOf E.obj L.obj a
            (c.hom ≫
              (D.finiteDimensionalModuleShiftUnderlyingIso
                (k := k) L a).hom)) =
        shiftOrbitOf L.obj L.obj a q := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  classical
  intro q c hc
  rw [shiftOrbitCompHom_of_of]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_zero a)
  apply (shiftHomComp_heq_shiftHomComp' (add_zero a)
    (shiftHomZero (A := Additive G) f.hom)
    (c.hom ≫
      (D.finiteDimensionalModuleShiftUnderlyingIso
        (k := k) L a).hom)).trans
  apply heq_of_eq
  rw [shiftHomComp'_zero_left]
  have hc' := congrArg (fun z ↦ z.hom) hc
  change f.hom ≫ c.hom =
    (finiteDimensionalShiftHom (k := k) D L L a q).hom at hc'
  rw [← Category.assoc, hc']
  exact finiteDimensionalShiftHom_roundtrip (k := k) D L L a q

variable [IsCancelSMul G C]

set_option backward.isDefEq.respectTransparency false in
/-- A split monomorphism after finite skeletal push-down was already split
upstairs.  A downstairs retraction is pulled back through the covering Hom
equivalence, and its degree-zero component retracts the original map. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_reflects_splitMono
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (f : M ⟶ N) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    IsSplitMono
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map f) →
      IsSplitMono f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro hsplit
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let q : ShiftOrbitHom (Additive G) M.obj N.obj :=
    shiftOrbitOf M.obj N.obj 0
      (shiftHomZero (A := Additive G) f.hom)
  let E_MN := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M N
  let E_NM := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) N M
  let E_MM := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M M
  have hq : E_MN q = P.map f :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
      (k := k) M N f
  letI : IsSplitMono (P.map f) := hsplit
  let r : ShiftOrbitHom (Additive G) N.obj M.obj :=
    E_NM.symm (retraction (P.map f))
  have hEid : E_MM (shiftOrbitId M.obj) = 𝟙 (P.obj M) := by
    rw [shiftOrbitId, ← shiftHomZero_id (A := Additive G)]
    exact (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
      (k := k) M M (𝟙 M)).trans (P.map_id M)
  have hcomp : shiftOrbitCompHom q r = shiftOrbitId M.obj := by
    apply E_MM.injective
    rw [← D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
      (k := k) M N M]
    rw [hq, E_NM.apply_symm_apply, hEid]
    exact IsSplitMono.id (P.map f)
  have hsplitOrbit : IsSplitMono
      (show (show ShiftOrbitCategory
          (LinearModuleCategory.{u, v, uK, uM} (C := C) k) (Additive G)
            from M.obj) ⟶
        (show ShiftOrbitCategory
          (LinearModuleCategory.{u, v, uK, uM} (C := C) k) (Additive G)
            from N.obj) from q) := by
    apply IsSplitMono.mk'
    exact ⟨r, hcomp⟩
  have hsplitLinear : IsSplitMono f.hom :=
    isSplitMono_of_shiftOrbit_zero_isSplitMono k f.hom hsplitOrbit
  letI : IsSplitMono f.hom := hsplitLinear
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  apply IsSplitMono.mk'
  refine ⟨J.preimage (retraction f.hom), ?_⟩
  apply J.map_injective
  rw [Functor.map_comp, J.map_preimage]
  change f.hom ≫ retraction f.hom = 𝟙 M.obj
  exact IsSplitMono.id f.hom

set_option backward.isDefEq.respectTransparency false in
/-- The terminal map of a pushed short exact sequence cannot split when the
upstairs initial map is left almost split. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_g_not_isSplitEpi
    (S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k))
    (hS : S.ShortExact) (hf : IsLeftAlmostSplit S.f) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ¬ IsSplitEpi
      ((S.map
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))).g) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  intro hg
  letI : IsSplitEpi ((S.map P).g) := hg
  have hPS : (S.map P).ShortExact :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_shortExact S hS
  have hPsplit : IsSplitMono ((S.map P).f) :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isSplitMono_f_of_isSplitEpi_g hPS
  have hup : IsSplitMono S.f :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_reflects_splitMono
      S.X₁ S.X₂ S.f hPsplit
  exact hf.not_isSplitMono hup

set_option backward.isDefEq.respectTransparency false in
/-- If every homogeneous component of a downstairs endomorphism is nonsplit
monic upstairs, an upstairs left almost-split injection factors the entire
endomorphism after finite skeletal push-down. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_leftEndomorphism_factor
    (L E : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (f : L ⟶ E) (hf : IsLeftAlmostSplit f)
    (q :
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (∀ a : Additive G,
      ¬ IsSplitMono
        (finiteDimensionalShiftHom (k := k) D L L a
          (((D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
            (k := k) L L).symm q) a))) →
      ∃ c :
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj E ⟶
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L,
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map f ≫ c = q := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let q' := (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) L L).symm q
  intro hcomp
  have hfac : ∀ a : Additive G, ∃ c : ShiftHom E.obj L.obj a,
      shiftOrbitCompHom
          (shiftOrbitOf L.obj E.obj 0
            (shiftHomZero (A := Additive G) f.hom))
          (shiftOrbitOf E.obj L.obj a c) =
        shiftOrbitOf L.obj L.obj a (q' a) := by
    intro a
    obtain ⟨c, hc⟩ := hf.factors
      (finiteDimensionalShiftHom (k := k) D L L a (q' a)) (hcomp a)
    exact ⟨c.hom ≫
        (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) L a).hom,
      shiftOrbitComponent_factor (k := k) D L E a f (q' a) c hc⟩
  obtain ⟨c', hc'⟩ :=
    exists_shiftOrbit_factor_of_components f.hom q' hfac
  refine ⟨D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
      (k := k) E L c', ?_⟩
  rw [← D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
    (k := k) L E f]
  rw [finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp]
  rw [hc']
  exact LinearEquiv.apply_symm_apply
    (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
      (k := k) L L) q

set_option backward.isDefEq.respectTransparency false in
/-- For an indecomposable with trivial deck stabilizer, nonsplitness of the
identity component of a downstairs endomorphism forces nonsplitness of every
homogeneous component. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_allComponents_not_isSplitMono_of_identity
    (L : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hL : Indecomposable L) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ q :
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L,
    (∀ a : Additive G, Nonempty (L ≅ L⟦a⟧) → a = 0) →
    ¬ IsSplitMono
      (finiteDimensionalShiftHom (k := k) D L L 0
        (((D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
          (k := k) L L).symm q) 0)) →
    ∀ a : Additive G,
      ¬ IsSplitMono
        (finiteDimensionalShiftHom (k := k) D L L a
          (((D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
            (k := k) L L).symm q) a)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro q htrivial hzero a
  by_cases ha : a = 0
  · subst a
    exact hzero
  · intro hsplit
    let qₐ := finiteDimensionalShiftHom (k := k) D L L a
      (((D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
        (k := k) L L).symm q) a)
    letI : IsSplitMono qₐ := hsplit
    have hshift : Indecomposable (L⟦a⟧) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor
          (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) a)
        L).mpr hL
    haveI : IsIso qₐ :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        hshift qₐ hL.1
    exact ha (htrivial a ⟨asIso qₐ⟩)

set_option backward.isDefEq.respectTransparency false in
/-- A noninvertible endomorphism of the pushed indecomposable has nonsplit
identity component upstairs.  This is Gabriel's identity-component
nilpotence/nonunit assertion, proved through the unique residue maps of the
two finite-dimensional local endomorphism algebras. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_identityComponent_not_isSplitMono
    [IsAlgClosed k]
    (L : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k)
    (hL : Indecomposable L) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, w}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (∀ a : Additive G, Nonempty (L ≅ L⟦a⟧) → a = 0) →
    ∀ q :
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L,
      ¬ IsIso q →
      ¬ IsSplitMono
        (finiteDimensionalShiftHom (k := k) D L L 0
          (((D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
            (k := k) L L).symm q) 0)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, w}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro htrivial q hq hsplit
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let PL := P.obj L
  let E := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) L L
  letI : IsLocalRing (End L.obj) :=
    finiteDimensionalModule_linearModule_end_isLocalRing k L hL
  have hLlinear : Indecomposable L.obj :=
    MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end L.obj
  have htrivialLinear : ∀ a : Additive G,
      Nonempty (L.obj ≅ L.obj⟦a⟧) → a = 0 :=
    finiteDimensionalModule_trivial_linear_stabilizer
      (k := k) D L htrivial
  let ρ := shiftOrbitResidueLinearMap
    (k := k) (A := Additive G) L.obj
  have hPL : Indecomposable PL :=
    finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) D L hL htrivial
  letI : IsLocalRing (End PL) :=
    finiteDimensionalModule_end_isLocalRing k PL hPL
  have hEone : E (shiftOrbitId L.obj) = (𝟙 PL) := by
    rw [shiftOrbitId, ← shiftHomZero_id (A := Additive G)]
    exact (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
      (k := k) L L (𝟙 L)).trans (P.map_id L)
  have hEsymm_one : E.symm (𝟙 PL) = shiftOrbitId L.obj := by
    apply E.injective
    rw [E.apply_symm_apply]
    exact hEone.symm
  have hEsymm_mul (x y : End PL) :
      E.symm (x * y) = shiftOrbitCompHom (E.symm y) (E.symm x) := by
    apply E.injective
    rw [E.apply_symm_apply]
    rw [← D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
      (k := k) L L L]
    rw [E.apply_symm_apply, E.apply_symm_apply]
    rfl
  let φ : End PL →ₐ[k] k :=
    { toFun := fun x ↦ ρ (E.symm x)
      map_zero' := by simp
      map_one' := by
        change ρ (E.symm (𝟙 PL)) = 1
        rw [hEsymm_one]
        exact shiftOrbitResidueLinearMap_one
          (k := k) (A := Additive G) L.obj
      map_add' := by
        intro x y
        change ρ (E.symm (x + y)) = ρ (E.symm x) + ρ (E.symm y)
        rw [map_add, map_add]
      map_mul' := by
        intro x y
        change ρ (E.symm (x * y)) = ρ (E.symm x) * ρ (E.symm y)
        rw [hEsymm_mul]
        rw [shiftOrbitResidueLinearMap_comp L.obj hLlinear htrivialLinear]
        exact mul_comm _ _
      commutes' := by
        intro c
        change ρ (E.symm (c • (𝟙 PL))) = c
        rw [map_smul, hEsymm_one, map_smul,
          shiftOrbitResidueLinearMap_one]
        simp }
  have hφ : φ = LocalAlgebraResidue.residueAlgHom k (End PL) :=
    LocalAlgebraResidue.algHom_eq_residueAlgHom φ
  have hqNonunit : ¬ IsUnit (End.of q) := by
    intro hunit
    exact hq ((isUnit_iff_isIso q).mp hunit)
  have hqResidue : LocalAlgebraResidue.residueScalar k (End.of q) = 0 :=
    (LocalAlgebraResidue.mem_ker_residueLinearMap_iff
      (k := k) (E := End PL) (End.of q)).mpr hqNonunit
  have horbitResidue :
      shiftOrbitResidueLinearMap (k := k) (A := Additive G) L.obj
        (E.symm q) = 0 := by
    change φ (End.of q) = 0
    rw [hφ]
    exact hqResidue
  let E₀ := shiftHomZeroLinearEquiv
    (k := k) (A := Additive G) L.obj L.obj
  have hidentityResidue :
      LocalAlgebraResidue.residueScalar k
        (End.of (E₀.symm ((E.symm q) 0))) = 0 := horbitResidue
  have hidentityNonunit : ¬ IsUnit (End.of (E₀.symm ((E.symm q) 0))) :=
    (LocalAlgebraResidue.mem_ker_residueLinearMap_iff
      (k := k) (E := End L.obj)
      (End.of (E₀.symm ((E.symm q) 0)))).mp hidentityResidue
  let q₀ := finiteDimensionalShiftHom (k := k) D L L 0 ((E.symm q) 0)
  letI : IsSplitMono q₀ := hsplit
  have hshift : Indecomposable (L⟦(0 : Additive G)⟧) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k) 0)
        L).mpr hL
  haveI : IsIso q₀ :=
    MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
      hshift q₀ hL.1
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  have hroundtrip : J.map q₀ ≫
      (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) L 0).hom =
        (E.symm q) 0 :=
    finiteDimensionalShiftHom_roundtrip (k := k) D L L 0 ((E.symm q) 0)
  haveI : IsIso ((E.symm q) 0) := by
    rw [← hroundtrip]
    infer_instance
  haveI : IsIso (E₀.symm ((E.symm q) 0)) := by
    change IsIso
      ((E.symm q) 0 ≫ (shiftFunctorZero
        (LinearModuleCategory.{u, v, uK, w} (C := C) k)
          (Additive G)).hom.app L.obj)
    infer_instance
  exact hidentityNonunit ((isUnit_iff_isIso _).mpr inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-- Every noninvertible endomorphism of the pushed left term factors through
the pushed left almost-split injection. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_leftEndomorphism_factor_of_trivial_stabilizer
    [IsAlgClosed k]
    (L E : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k)
    (hL : Indecomposable L) (f : L ⟶ E) (hf : IsLeftAlmostSplit f) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, w}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (∀ a : Additive G, Nonempty (L ≅ L⟦a⟧) → a = 0) →
    ∀ q :
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L,
      ¬ IsIso q →
      ∃ c :
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj E ⟶
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj L,
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map f ≫ c = q := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, w}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro htrivial q hq
  apply finiteDimensionalModuleOrbitSkeletonPushdown_leftEndomorphism_factor
    (k := k) D L E f hf q
  exact
    finiteDimensionalModuleOrbitSkeletonPushdown_allComponents_not_isSplitMono_of_identity
      (k := k) D L hL q htrivial
        (finiteDimensionalModuleOrbitSkeletonPushdown_identityComponent_not_isSplitMono
          (k := k) D L hL htrivial q hq)

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
