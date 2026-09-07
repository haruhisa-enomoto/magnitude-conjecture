import MagnitudeConjecture.Algebra.RightModuleProjectiveCover
import MagnitudeConjecture.Algebra.RightModuleSupportRingelVanishing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The finite-projective Nakayama kernel criterion

For a finitely generated projective right module `P`, this file constructs
the concrete Nakayama object

`nu P = D Hom_B(P, B)`.

A finite dual frame proves that the canonical map
`P -> Hom_B(D(B), nu P)` is injective and natural in `P`.  Consequently, if
`Hom_B(D(B), ker (nu d)) = 0`, then a morphism `d` between finitely generated
projectives is monic.  Applied to the first differential in a minimal
projective presentation, this is Ringel's projective-dimension-one argument.

Only the finite-frame construction pattern is adapted from the
equidistribution formalization.  The latter's Auslander-transpose and OP
layers are neither imported nor copied.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

/-- A finite dual frame for a finitely generated projective module. -/
structure FiniteProjectiveFrame
    (R P : Type u) [Semiring R] [AddCommMonoid P] [Module R P] where
  n : ℕ
  p : Fin n → P
  phi : Fin n → (P →ₗ[R] R)
  total : ∀ x : P, ∑ i, phi i x • p i = x

/-- A finite dual frame obtained from a finite free splitting. -/
def finiteProjectiveFrame
    (R P : Type u) [Semiring R] [AddCommMonoid P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    FiniteProjectiveFrame R P := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R P
  let n := h.choose
  let hf := h.choose_spec
  let f := hf.choose
  let hg := hf.choose_spec
  let g := hg.choose
  let hfg := hg.choose_spec.2.2
  let b := Pi.basisFun R (Fin n)
  refine
    { n := n
      p := fun i ↦ f (b i)
      phi := fun i ↦ (LinearMap.proj i).comp g
      total := ?_ }
  intro x
  calc
    ∑ i, ((LinearMap.proj i).comp g) x • f (b i) =
        f (∑ i, (b.repr (g x)) i • b i) := by
          rw [map_sum]
          congr 1
          funext i
          rw [map_smul]
          simp [b, Pi.basisFun_repr]
    _ = f (g x) := by rw [b.sum_repr]
    _ = x := by exact LinearMap.congr_fun hfg x

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

/-- The regular Hom-dual of a finite right module, with its natural left
`B`-action. -/
abbrev regularHomDualCarrier (P : FGModuleCat.{u} Bᵐᵒᵖ) :=
  P →ₗ[Bᵐᵒᵖ] B

omit [IsNoetherianRing Bᵐᵒᵖ] in
private theorem regularHomDualCarrier_finite (k : Type u)
    [Field k] [Algebra k B] [FiniteDimensional k B]
    (P : FGModuleCat.{u} Bᵐᵒᵖ) :
    Module.Finite B (regularHomDualCarrier P) := by
  letI : Module k P := Module.restrictScalars k Bᵐᵒᵖ P
  letI : IsScalarTower k Bᵐᵒᵖ P :=
    IsScalarTower.restrictScalars k Bᵐᵒᵖ P
  letI : Module.Finite k P := Module.Finite.trans Bᵐᵒᵖ P
  let toK : regularHomDualCarrier P →ₗ[k] (P →ₗ[k] B) :=
    { toFun := fun f ↦ f.restrictScalars k
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hfiniteK : Module.Finite k (regularHomDualCarrier P) :=
    Module.Finite.of_injective toK (by
      intro f g h
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun h x)
  exact Module.Finite.of_restrictScalars_finite k B (regularHomDualCarrier P)

/-- The regular Hom-dual bundled as a finitely generated left module. -/
abbrev regularHomDualFGObj (k : Type u) [Field k] [Algebra k B]
    [FiniteDimensional k B] (P : FGModuleCat.{u} Bᵐᵒᵖ) :
    FGModuleCat.{u} B := by
  letI : Module.Finite B (regularHomDualCarrier P) :=
    regularHomDualCarrier_finite (k := k) P
  exact FGModuleCat.of B (regularHomDualCarrier P)

/-- Precomposition is the contravariant map on regular Hom-duals. -/
def regularHomDualMap {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (d : P ⟶ Q) :
    regularHomDualFGObj (k := k) Q ⟶
      regularHomDualFGObj (k := k) P :=
  ConcreteCategory.ofHom
    { toFun := fun phi ↦ phi.comp d.hom.hom
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Evaluation at `p`, as a left-module map from the regular Hom-dual to
the left regular module. -/
def regularHomEvaluation (P : FGModuleCat.{u} Bᵐᵒᵖ) (p : P) :
    regularHomDualFGObj (k := k) P ⟶ leftRegularFGObj (B := B) :=
  ConcreteCategory.ofHom
    { toFun := fun phi ↦ phi p
      map_add' := by intros; simp
      map_smul' := by intros; rfl }

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem regularHomDualMap_comp_evaluation
    {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (d : P ⟶ Q) (p : P) :
    regularHomDualMap (k := k) d ≫ regularHomEvaluation (k := k) P p =
      regularHomEvaluation (k := k) Q (d.hom.hom p) := by
  apply FGModuleCat.hom_ext
  rfl

/-- The concrete Nakayama object `D Hom_B(P,B)`. -/
abbrev projectiveNakayamaFGObj (P : FGModuleCat.{u} Bᵐᵒᵖ) :
    FGModuleCat.{u} Bᵐᵒᵖ :=
  (Contragredient.dualFunctor k B).obj
    (Opposite.op (regularHomDualFGObj (k := k) P))

/-- The covariant Nakayama map induced by a morphism of right modules. -/
def projectiveNakayamaMap {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (d : P ⟶ Q) :
    projectiveNakayamaFGObj (k := k) P ⟶
      projectiveNakayamaFGObj (k := k) Q :=
  (Contragredient.dualFunctor k B).map
    (regularHomDualMap (k := k) d).op

/-- An element `p : P` determines the corresponding morphism
`D(B) -> nu P`. -/
def nakayamaUnitElement (P : FGModuleCat.{u} Bᵐᵒᵖ) (p : P) :
    injectiveCogeneratorFGObj (k := k) (B := B) ⟶
      projectiveNakayamaFGObj (k := k) P :=
  (Contragredient.dualFunctor k B).map
    (regularHomEvaluation (k := k) P p).op

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem nakayamaUnitElement_naturality
    {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (d : P ⟶ Q) (p : P) :
    nakayamaUnitElement (k := k) P p ≫ projectiveNakayamaMap (k := k) d =
      nakayamaUnitElement (k := k) Q (d.hom.hom p) := by
  change
    (Contragredient.dualFunctor k B).map
          (regularHomEvaluation (k := k) P p).op ≫
        (Contragredient.dualFunctor k B).map
          (regularHomDualMap (k := k) d).op =
      (Contragredient.dualFunctor k B).map
        (regularHomEvaluation (k := k) Q (d.hom.hom p)).op
  rw [← (Contragredient.dualFunctor k B).map_comp]
  congr 1

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem nakayamaUnitElement_zero (P : FGModuleCat.{u} Bᵐᵒᵖ) :
    nakayamaUnitElement (k := k) P 0 = 0 := by
  apply FGModuleCat.hom_ext
  apply DFunLike.ext _ _
  intro ell
  apply (Contragredient.forwardInnerDualEquiv k B
    (regularHomDualFGObj (k := k) P)).injective
  apply DFunLike.ext _ _
  intro phi
  change (Contragredient.forwardInnerDualEquiv k B
    (leftRegularFGObj (B := B)) ell) (phi 0) = 0
  rw [map_zero]
  exact map_zero _

/-- The element-to-Nakayama-Hom map is injective on every finite projective
right module. -/
theorem nakayamaUnitElement_injective
    (P : FGModuleCat.{u} Bᵐᵒᵖ) (hP : Projective P) :
    Function.Injective (nakayamaUnitElement (k := k) P) := by
  classical
  letI : Projective P := hP
  letI : Module.Projective Bᵐᵒᵖ P :=
    moduleProjective_of_fgProjective P hP
  let F := finiteProjectiveFrame Bᵐᵒᵖ P
  intro p q hpq
  have heval : regularHomEvaluation (k := k) P p =
      regularHomEvaluation (k := k) P q := by
    have hmap :
        (Contragredient.dualFunctor k B).map
            (regularHomEvaluation (k := k) P p).op =
          (Contragredient.dualFunctor k B).map
            (regularHomEvaluation (k := k) P q).op := hpq
    have hop : (regularHomEvaluation (k := k) P p).op =
        (regularHomEvaluation (k := k) P q).op := by
      apply (Contragredient.dualityEquivalence k B).functor.map_injective
      change
        (Contragredient.dualFunctor k B).map
            (regularHomEvaluation (k := k) P p).op =
          (Contragredient.dualFunctor k B).map
            (regularHomEvaluation (k := k) P q).op
      exact hmap
    exact Quiver.Hom.op_inj hop
  have hphi : ∀ i, F.phi i p = F.phi i q := by
    intro i
    let phiB : P →ₗ[Bᵐᵒᵖ] B :=
      RightModule.rightRegularLinearEquiv.toLinearMap.comp (F.phi i)
    have h := congrArg
      (fun f : regularHomDualFGObj (k := k) P ⟶
          leftRegularFGObj (B := B) ↦ f.hom.hom phiB) heval
    change (F.phi i p).unop = (F.phi i q).unop at h
    exact MulOpposite.unop_injective h
  calc
    p = ∑ i, F.phi i p • F.p i := (F.total p).symm
    _ = ∑ i, F.phi i q • F.p i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hphi i]
    _ = q := F.total q

/-- Vanishing of maps from the standard injective cogenerator to the
Nakayama kernel forces the original projective morphism to be monic. -/
theorem mono_of_hom_from_injectiveCogenerator_to_nakayamaKernel_eq_zero
    {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (d : P ⟶ Q)
    (hP : Projective P)
    (hzero : ∀ q : injectiveCogeneratorFGObj (k := k) (B := B) ⟶
        kernel (projectiveNakayamaMap (k := k) d), q = 0) :
    Mono d := by
  apply (IndecomposableSkeleton.fg_mono_iff_injective d).2
  have kernelZero : ∀ p : P, d.hom.hom p = 0 → p = 0 := by
    intro p hp
    have hcomp : nakayamaUnitElement (k := k) P p ≫
        projectiveNakayamaMap (k := k) d = 0 := by
      rw [nakayamaUnitElement_naturality, hp,
        nakayamaUnitElement_zero]
    let q := kernel.lift (projectiveNakayamaMap (k := k) d)
      (nakayamaUnitElement (k := k) P p) hcomp
    have hq : q = 0 := hzero q
    have hunitZero : nakayamaUnitElement (k := k) P p = 0 := by
      rw [← kernel.lift_ι (projectiveNakayamaMap (k := k) d)
        (nakayamaUnitElement (k := k) P p) hcomp]
      change q ≫ kernel.ι (projectiveNakayamaMap (k := k) d) = 0
      rw [hq, zero_comp]
    apply nakayamaUnitElement_injective (k := k) P hP
    simpa using hunitZero
  intro p q hpq
  apply sub_eq_zero.mp
  apply kernelZero (p - q)
  rw [map_sub, hpq, sub_self]

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.TwoStepMinimalProjectivePresentation

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable {X : FGModuleCat.{u} Bᵐᵒᵖ}

/-- Applying the concrete Nakayama construction to the first differential
of a two-step minimal projective presentation. -/
def nakayamaDifferential (P : TwoStepMinimalProjectivePresentation X) :
    RightModule.projectiveNakayamaFGObj (k := k)
        P.syzygyPresentation.p ⟶
      RightModule.projectiveNakayamaFGObj (k := k) P.augmentation.p :=
  RightModule.projectiveNakayamaMap (k := k) P.differential

/-- Ringel's Nakayama kernel attached to the chosen minimal presentation. -/
abbrev nakayamaKernel (P : TwoStepMinimalProjectivePresentation X) :
    FGModuleCat.{u} Bᵐᵒᵖ :=
  kernel (P.nakayamaDifferential (k := k))

/-- The literal Nakayama-kernel vanishing implies projective dimension at
most one. -/
theorem hasProjectiveDimensionLE_one_of_hom_from_injectiveCogenerator_to_nakayamaKernel_eq_zero
    (P : TwoStepMinimalProjectivePresentation X)
    (hzero : ∀ q : RightModule.injectiveCogeneratorFGObj (k := k) (B := B) ⟶
        P.nakayamaKernel (k := k), q = 0) :
    HasProjectiveDimensionLE X 1 := by
  apply P.hasProjectiveDimensionLE_one_of_mono_differential
  exact RightModule.mono_of_hom_from_injectiveCogenerator_to_nakayamaKernel_eq_zero
    (k := k) P.differential inferInstance hzero

/-- It is enough to identify an external module with the Nakayama kernel
and prove the cogenerator vanishing for that module.  This is the interface
used to connect the chosen almost-split kernel to Ringel's construction. -/
theorem hasProjectiveDimensionLE_one_of_nakayamaKernelIso_of_hom_eq_zero
    (P : TwoStepMinimalProjectivePresentation X)
    {T : FGModuleCat.{u} Bᵐᵒᵖ}
    (e : T ≅ P.nakayamaKernel (k := k))
    (hzero : ∀ q : RightModule.injectiveCogeneratorFGObj (k := k) (B := B) ⟶ T,
      q = 0) :
    HasProjectiveDimensionLE X 1 := by
  apply P.hasProjectiveDimensionLE_one_of_hom_from_injectiveCogenerator_to_nakayamaKernel_eq_zero
    (k := k)
  intro q
  apply (cancel_mono e.inv).1
  simpa using hzero (q ≫ e.inv)

end MagnitudeConjecture.TwoStepMinimalProjectivePresentation

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- The literal support-algebra endpoint in the chosen right almost-split
sequence. -/
abbrev rightSequenceSupportEndpointFGObj
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :=
  (P.supportAlgebraSkeleton hA
    (S.minimalRightAlmostSplitAt z.1).middle).fgObj
      (P.rightSequenceSupportTargetLabel hA z)

/-- The literal selected representative of the support almost-split
kernel. -/
abbrev rightSequenceSupportKernelFGObj
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :=
  (P.supportAlgebraSkeleton hA
    (S.minimalRightAlmostSplitAt z.1).middle).fgObj
      (P.rightSequenceSupportKernelLabel hA z)

/-- Once the standard `DTr` identification is supplied for a minimal
presentation of the support endpoint, the already established directed
vanishing proves Ringel's projective-dimension-one conclusion. -/
theorem rightSequenceSupportEndpoint_hasProjectiveDimensionLE_one_of_nakayamaKernelIso
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (Q : TwoStepMinimalProjectivePresentation
      (P.rightSequenceSupportEndpointFGObj hA z))
    (e : P.rightSequenceSupportKernelFGObj hA z ≅
      Q.nakayamaKernel (k := k)) :
    HasProjectiveDimensionLE (P.rightSequenceSupportEndpointFGObj hA z) 1 := by
  apply Q.hasProjectiveDimensionLE_one_of_nakayamaKernelIso_of_hom_eq_zero
    (k := k) e
  exact P.hom_from_supportInjectiveCogenerator_to_rightKernel_eq_zero hA H z

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
