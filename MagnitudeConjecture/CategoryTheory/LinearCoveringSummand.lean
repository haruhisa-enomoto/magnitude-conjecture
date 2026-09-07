import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaHom
import MagnitudeConjecture.CategoryTheory.LinearCoveringPullback

/-!
# Isolating a representable summand in a covering pullback

For a Hom-finite linear category, coefficient-dual corepresentables retain
the local endomorphism rings of their representing objects.  This permits the
finite-support local-ring argument which isolates one dual-corepresentable
from an isomorphism between fixed-fibre direct sums.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uD vD

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

private def endRingEquivOfFullyFaithful
    {E : Type uD} [Category.{vD} E] [Preadditive E]
    (G : Cᵒᵖ ⥤ E) [G.Additive] [G.Full] [G.Faithful] (X : Cᵒᵖ) :
    End X ≃+* End (G.obj X) where
  toFun := G.map
  invFun := G.preimage
  left_inv := G.preimage_map
  right_inv := G.map_preimage
  map_add' _ _ := G.map_add
  map_mul' f g := G.map_comp g f

private def oppositeEndRingEquiv (X : C) :
    (End X)ᵐᵒᵖ ≃+* End (Opposite.op X) where
  toFun f := f.unop.op
  invFun f := MulOpposite.op f.unop
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; apply Quiver.Hom.unop_inj; rfl
  map_mul' := by intro f g; apply Quiver.Hom.unop_inj; rfl

private theorem isLocalRing_mulOpposite
    {R : Type v} [Ring R] [IsLocalRing R] :
    IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

/-- A covariant linear representable has local endomorphism ring when its
representing object does. -/
theorem linearCoyonedaLinearModule_end_isLocalRing
    (X : C) (hlocal : IsLocalRing (End X)) :
    IsLocalRing (End (linearCoyonedaLinearModule (k := k) X)) := by
  letI : IsLocalRing (End X) := hlocal
  letI : IsLocalRing (End X)ᵐᵒᵖ := isLocalRing_mulOpposite
  letI : IsLocalRing (End (Opposite.op X)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (oppositeEndRingEquiv X)
  let F := linearCoyonedaLinearModuleFunctor (k := k) (C := C)
  letI : F.Full := by
    dsimp [F, linearCoyonedaLinearModuleFunctor]
    infer_instance
  letI : F.Faithful := by
    dsimp [F, linearCoyonedaLinearModuleFunctor]
    infer_instance
  change IsLocalRing (End (F.obj (Opposite.op X)))
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (endRingEquivOfFullyFaithful F (Opposite.op X))

/-- Evaluation at the identity exposes the representing morphism underlying
the dual-corepresentable functor map. -/
@[simp]
theorem dualLinearYonedaHomEquiv_functor_map_apply
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (phi :
      (dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).obj X |>.obj.obj
        Y.unop) :
    dualLinearYonedaHomEquiv
        ((dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).obj X)
        Y.unop
        ((dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).map f) phi =
      (show Module.Dual k (Y.unop ⟶ X.unop) from phi) f.unop := by
  change (CategoryTheory.Linear.rightComp k Y.unop f.unop).dualMap
      (show Module.Dual k (Y.unop ⟶ X.unop) from phi) (𝟙 Y.unop) = _
  rw [LinearMap.dualMap_apply]
  simp

/-- The dual-corepresentable functor is faithful over a field. -/
theorem dualLinearYonedaLinearModuleFunctor_faithful :
    (dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).Faithful := by
  constructor
  intro X Y f g hfg
  apply Quiver.Hom.unop_inj
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro phi
  have happ := congrArg
    (fun a :
        (dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).obj X ⟶
          (dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).obj Y ↦
      dualLinearYonedaHomEquiv
        ((dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).obj X)
        Y.unop a phi) hfg
  simpa using happ

/-- Hom-finiteness makes the dual-corepresentable functor full by
finite-dimensional double duality. -/
theorem dualLinearYonedaLinearModuleFunctor_full
    (hfinite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)) :
    (dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).Full := by
  constructor
  intro X Y a
  let V := Y.unop ⟶ X.unop
  letI : FiniteDimensional k V := hfinite Y.unop X.unop
  let ell : Module.Dual k (Module.Dual k V) :=
    dualLinearYonedaHomEquiv
      ((dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).obj X)
      Y.unop a
  let q : V := (Module.evalEquiv k V).symm ell
  refine ⟨q.op, ?_⟩
  apply (dualLinearYonedaHomEquiv
    ((dualLinearYonedaLinearModuleFunctor (k := k) (C := C)).obj X)
    Y.unop).injective
  apply LinearMap.ext
  intro phi
  rw [dualLinearYonedaHomEquiv_functor_map_apply]
  change (show Module.Dual k V from phi) q =
    ell (show Module.Dual k V from phi)
  exact LinearMap.congr_fun
    ((Module.evalEquiv k V).apply_symm_apply ell)
      (show Module.Dual k V from phi)

/-- A dual linear corepresentable has local endomorphism ring when the
category is Hom-finite and its representing object has local endomorphism
ring. -/
theorem dualLinearYonedaLinearModule_end_isLocalRing
    (hfinite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y))
    (X : C) (hlocal : IsLocalRing (End X)) :
    IsLocalRing (End (dualLinearYonedaLinearModule (k := k) X)) := by
  letI : IsLocalRing (End X) := hlocal
  letI : IsLocalRing (End X)ᵐᵒᵖ := isLocalRing_mulOpposite
  letI : IsLocalRing (End (Opposite.op X)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (oppositeEndRingEquiv X)
  let F := dualLinearYonedaLinearModuleFunctor (k := k) (C := C)
  letI : F.Full := dualLinearYonedaLinearModuleFunctor_full hfinite
  letI : F.Faithful := dualLinearYonedaLinearModuleFunctor_faithful
  change IsLocalRing (End (F.obj (Opposite.op X)))
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (endRingEquivOfFullyFaithful F (Opposite.op X))

/-- Under the same hypotheses, a dual linear corepresentable is
indecomposable. -/
theorem dualLinearYonedaLinearModule_indecomposable
    (hfinite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y))
    (X : C) (hlocal : IsLocalRing (End X)) :
    Indecomposable (dualLinearYonedaLinearModule (k := k) X) := by
  letI : IsLocalRing
      (End (dualLinearYonedaLinearModule (k := k) X)) :=
    dualLinearYonedaLinearModule_end_isLocalRing hfinite X hlocal
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.LinearCovering

universe u

variable {k : Type u} [Field k]
variable {C D : Type} [Category.{u} C] [Category.{u} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- If the fixed-source representable sum is isomorphic to a fixed-target
sum of dual corepresentables, a chosen local source summand is isomorphic to
one target summand.  Finiteness comes from the support of the image of the
source identity. -/
theorem exists_dualCorepresentable_iso_of_fiberSumIso
    {X Z : D} (P : Fiber F X)
    (e : sourceFiberRepresentableLinearModule (k := k) F X ≅
      targetFiberDualCorepresentableLinearModule (k := k) F Z)
    (hfinite : ∀ Y W : C, FiniteDimensional k (Y ⟶ W))
    (hlocal : ∀ Y : C, IsLocalRing (End Y)) :
    ∃ J : Fiber F Z, Nonempty
      (CoveringHom.linearCoyonedaLinearModule (k := k) P.1 ≅
        CoveringHom.dualLinearYonedaLinearModule (k := k) J.1) := by
  classical
  let R := CoveringHom.linearCoyonedaLinearModule (k := k) P.1
  let Q (J : Fiber F Z) :=
    CoveringHom.dualLinearYonedaLinearModule (k := k) J.1
  let i : R ⟶ sourceFiberRepresentableLinearModule (k := k) F X :=
    sourceFiberRepresentableInclusion (k := k) F X P
  let r : sourceFiberRepresentableLinearModule (k := k) F X ⟶ R :=
    sourceFiberRepresentableProjection (k := k) F X P
  let alpha : R ⟶ targetFiberDualCorepresentableLinearModule (k := k) F Z :=
    i ≫ e.hom
  let beta : targetFiberDualCorepresentableLinearModule (k := k) F Z ⟶ R :=
    e.inv ≫ r
  have hab : alpha ≫ beta = 𝟙 R := by
    calc
      alpha ≫ beta = i ≫ r := by simp [alpha, beta, Category.assoc]
      _ = 𝟙 R := by
        change sourceFiberRepresentableInclusion (k := k) F X P ≫
            sourceFiberRepresentableProjection (k := k) F X P = 𝟙 R
        exact sourceFiberRepresentableInclusion_projection (k := k) F X P
  let x : DirectSum (Fiber F Z)
      (fun J ↦ Module.Dual k (P.1 ⟶ J.1)) :=
    alpha.hom.app P.1 (𝟙 P.1)
  let a (J : Fiber F Z) : R ⟶ Q J :=
    alpha ≫ targetFiberDualCorepresentableProjection (k := k) F Z J
  let b (J : Fiber F Z) : Q J ⟶ R :=
    targetFiberDualCorepresentableInclusion (k := k) F Z J ≫ beta
  let c (J : Fiber F Z) : End R := a J ≫ b J
  have hsum : ∑ J ∈ x.support, c J = 𝟙 R := by
    rw [← hab]
    apply (CoveringHom.linearCoyonedaHomEquiv R P.1).injective
    simp only [map_sum]
    change
      (∑ J ∈ x.support,
        beta.hom.app P.1
          (DirectSum.of
            (fun L : Fiber F Z ↦ Module.Dual k (P.1 ⟶ L.1)) J (x J))) =
        beta.hom.app P.1 x
    rw [← map_sum, DirectSum.sum_support_of]
  letI : IsLocalRing (End R) :=
    CoveringHom.linearCoyonedaLinearModule_end_isLocalRing P.1 (hlocal P.1)
  have hunit : IsUnit (∑ J ∈ x.support, c J) := by
    rw [hsum]
    exact isUnit_one
  obtain ⟨J, _hJ, hJunit⟩ :=
    IsLocalRing.exists_of_isUnit_sum (s := x.support) (f := c) hunit
  have hcIso : IsIso (a J ≫ b J) := by
    apply (isUnit_iff_isIso (a J ≫ b J)).1
    simpa only [c] using hJunit
  letI : IsIso (a J ≫ b J) := hcIso
  letI : IsSplitMono (a J) := by
    apply IsSplitMono.mk'
    exact
      { retraction := b J ≫ inv (a J ≫ b J)
        id := by rw [← Category.assoc, IsIso.hom_inv_id] }
  have hQ : Indecomposable (Q J) :=
    CoveringHom.dualLinearYonedaLinearModule_indecomposable
      hfinite J.1 (hlocal J.1)
  have hR : Indecomposable R := by
    exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _
  haveI : IsIso (a J) :=
    MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
      hQ (a J) hR.1
  exact ⟨J, ⟨asIso (a J)⟩⟩

end MagnitudeConjecture.LinearCovering
