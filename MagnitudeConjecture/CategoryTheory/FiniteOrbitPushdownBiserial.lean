import MagnitudeConjecture.CategoryTheory.BiserialObject
import MagnitudeConjecture.CategoryTheory.ExactFunctorSubobject
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownUniserial

/-!
# Biserial finite representables under finite orbit push-down

For a finite representable, the radical inclusion is monic and right almost
split.  Its push-down has the same property.  Exactness transports the join
and intersection of two radical branches, while preservation of uniserial
and simple finite modules transports the remaining branch conditions.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G]
variable [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Finite skeletal Gabriel push-down sends a biserial finite representable
to a biserial object. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_biserial_representable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (X : C)
    (hX : IsBiserialObject
      (finiteDimensionalLinearCoyoneda (k := k) X (hP X))) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    IsBiserialObject
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (finiteDimensionalLinearCoyoneda (k := k) X (hP X))) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let P := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
  let r := finiteDimensionalLinearCoyonedaRadicalInclusion
    (k := k) X (hP X)
  rcases hX with ⟨R, U, V, hR, hR_unique, hsup, hU, hV, hinter⟩
  have hr : IsRightAlmostSplit r :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP hlocal X
  have hR_literal : Subobject.mk r = R :=
    hR_unique (Subobject.mk r)
      (isCoatom_mk_of_mono_rightAlmostSplit r hr)
  have hFr : IsRightAlmostSplit (F.map r) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion_isRightAlmostSplit
      (k' := k) hP hlocal hfree X
  let RD := Functor.mapSubobject F R
  let UD := Functor.mapSubobject F U
  let VD := Functor.mapSubobject F V
  have hRD_eq : RD = Subobject.mk (F.map r) := by
    dsimp only [RD]
    rw [← hR_literal, Functor.mapSubobject_mk]
  have hRD : IsCoatom RD := by
    rw [hRD_eq]
    exact isCoatom_mk_of_mono_rightAlmostSplit (F.map r) hFr
  have hRD_radical : IsUniserialObject.IsRadicalSubobject RD := by
    rw [hRD_eq]
    exact isRadicalSubobject_mk_of_mono_rightAlmostSplit (F.map r) hFr
  have hRD_unique : ∀ Q : Subobject (F.obj P), IsCoatom Q → Q = RD := by
    intro Q hQ
    have hQR : Q ≤ RD := hRD_radical Q hQ.ne_top
    exact ((hQ.le_iff_eq hRD.ne_top).mp hQR).symm
  have hsum : UD ⊔ VD = RD := by
    dsimp only [UD, VD, RD]
    rw [← Functor.mapSubobject_sup F U V, hsup]
  have hUobj : IsUniserialObject (U :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    (IsUniserialObject.subobject_iff_total_Iic U).mpr hU
  have hVobj : IsUniserialObject (V :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    (IsUniserialObject.subobject_iff_total_Iic V).mpr hV
  have hFU : IsUniserialObject (F.obj (U :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_uniserial
      hP hlocal hfree (U :
        FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) hUobj
  have hFV : IsUniserialObject (F.obj (V :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_uniserial
      hP hlocal hfree (V :
        FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) hVobj
  have hUDobj : IsUniserialObject (UD :
      FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    hFU.congr (Functor.mapSubobjectUnderlyingIso F U).symm
  have hVDobj : IsUniserialObject (VD :
      FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    hFV.congr (Functor.mapSubobjectUnderlyingIso F V).symm
  have hUD : Std.Total ((· ≤ ·) : Set.Iic UD → Set.Iic UD → Prop) :=
    (IsUniserialObject.subobject_iff_total_Iic UD).mp hUDobj
  have hVD : Std.Total ((· ≤ ·) : Set.Iic VD → Set.Iic VD → Prop) :=
    (IsUniserialObject.subobject_iff_total_Iic VD).mp hVDobj
  have hinterD : UD ⊓ VD = ⊥ ∨ IsAtom (UD ⊓ VD) := by
    rcases hinter with hbot | hatom
    · left
      rw [← Functor.mapSubobject_inf F U V, hbot,
        Functor.mapSubobject_bot]
    · right
      let W := U ⊓ V
      have hWsimple : Simple (W :
          FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
        (subobject_simple_iff_isAtom W).mpr hatom
      have hFWsimple : Simple (F.obj (W :
          FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)) :=
        D.finiteDimensionalModuleOrbitSkeletonPushdown_simple
          hP hlocal hfree (W :
            FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
          hWsimple
      let WD := Functor.mapSubobject F W
      have hWDsimple : Simple (WD :
          FiniteDimensionalModuleCategory.{u, v, v, v}
            (C := DeckOrbitSkeleton C G) k) := by
        letI : Simple (F.obj (W :
            FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)) :=
          hFWsimple
        exact Simple.of_iso (Functor.mapSubobjectUnderlyingIso F W)
      have hmeet : WD = UD ⊓ VD := by
        dsimp only [WD, W, UD, VD]
        exact Functor.mapSubobject_inf F U V
      rw [← hmeet]
      exact (subobject_simple_iff_isAtom WD).mp hWDsimple
  exact ⟨RD, UD, VD, hRD, hRD_unique, hsum, hUD, hVD, hinterD⟩

/-- Equivalently, the representable at the orbit of an upstairs object is
biserial. -/
theorem finiteDimensionalLinearCoyoneda_orbitSkeleton_biserial
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (X : C)
    (hX : IsBiserialObject
      (finiteDimensionalLinearCoyoneda (k := k) X (hP X))) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
    let Q : DeckOrbitSkeleton C G :=
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
    IsBiserialObject
      (finiteDimensionalLinearCoyoneda (k := k) Q (hP' Q)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let Q : DeckOrbitSkeleton C G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
  have hpush :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_biserial_representable
      hP hlocal hfree X hX
  exact hpush.congr
    (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X (hP X))

/-- If all upstairs finite representables are biserial, then every finite
representable on the strict orbit skeleton is biserial. -/
theorem orbitSkeleton_finiteDimensionalLinearCoyoneda_biserial
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hall : ∀ X : C, IsBiserialObject
      (finiteDimensionalLinearCoyoneda (k := k) X (hP X)))
    (q : MulAction.orbitRel.Quotient G C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
    let Q : DeckOrbitSkeleton C G := q
    IsBiserialObject
      (finiteDimensionalLinearCoyoneda (k := k) Q (hP' Q)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let Q : DeckOrbitSkeleton C G := q
  let X := deckOrbitRepresentative (C := C) (G := G)
    q
  have h := D.finiteDimensionalLinearCoyoneda_orbitSkeleton_biserial
    hP hlocal hfree X (hall X)
  dsimp only [Q]
  rw [← deckOrbitRepresentative_mk (C := C) (G := G) q]
  exact h

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
