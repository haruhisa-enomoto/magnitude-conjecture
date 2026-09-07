import MagnitudeConjecture.Algebra.StringDetectorSubspace
import MagnitudeConjecture.Algebra.StringPolarization

/-!
# Boundary subspaces for string detectors

For a Butler--Ringel endpoint word `C`, the lower subspace `C^-` starts with
the image of the unique compatible incoming arrow, or zero if there is none.
The upper subspace `C^+` starts with the kernel of the unique compatible
outgoing arrow, or the whole source space if there is none.  Both are then
transported along `C`.

The polarization selects the correct one of the at most two arrows at a
trivial endpoint.  For a nontrivial word the same sign condition is forced by
string composability.  This file proves the fundamental inclusion
`C^-(M) <= C^+(M)` and its naturality under module morphisms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u : Q} {t : Bool}

namespace EndpointWord

/-- An incoming ordinary arrow which can be placed immediately before `C`
with the Butler--Ringel endpoint-sign convention. -/
abbrev IncomingExtension (C : EndpointWord S u t) :=
  {inc : Quiver.Costar C.source //
    IsString P.toPresentation.relations
        ((positiveArrow inc.2).toPath.comp C.path) ∧
      C.sourceSign = Bool.not (S.targetSign inc.2)}

/-- An outgoing ordinary arrow whose formal inverse can be placed immediately
before `C` with the Butler--Ringel endpoint-sign convention. -/
abbrev OutgoingInverseExtension (C : EndpointWord S u t) :=
  {out : Quiver.Star C.source //
    IsString P.toPresentation.relations
        ((negativeArrow out.2).toPath.comp C.path) ∧
      C.sourceSign = Bool.not (S.sourceSign out.2)}

/-- The endpoint sign selects at most one compatible incoming arrow. -/
theorem incomingExtension_subsingleton (C : EndpointWord S u t) :
    Subsingleton C.IncomingExtension := by
  constructor
  rintro ⟨inc₁, _, hsign₁⟩ ⟨inc₂, _, hsign₂⟩
  apply Subtype.ext
  apply (S.atVertex C.source).targetSign_injective
  apply Bool.involutive_not.injective
  exact hsign₁.symm.trans hsign₂

/-- The endpoint sign selects at most one compatible outgoing inverse. -/
theorem outgoingInverseExtension_subsingleton (C : EndpointWord S u t) :
    Subsingleton C.OutgoingInverseExtension := by
  constructor
  rintro ⟨out₁, _, hsign₁⟩ ⟨out₂, _, hsign₂⟩
  apply Subtype.ext
  apply (S.atVertex C.source).sourceSign_injective
  apply Bool.involutive_not.injective
  exact hsign₁.symm.trans hsign₂

/-- If both boundary extensions exist, their ordinary two-arrow composition
is killed by the relations. -/
theorem outgoing_comp_incoming_eq_zero
    (C : EndpointWord S u t)
    (inc : C.IncomingExtension)
    (out : C.OutgoingInverseExtension) :
    arrowMap P.toPresentation.relations out.1.2 ≫
        arrowMap P.toPresentation.relations inc.1.2 = 0 := by
  by_contra hcomp
  have hopposite := S.sourceSign_eq_not_targetSign
    inc.1.2 out.1.2 hcomp
  have hequal : S.targetSign inc.1.2 = S.sourceSign out.1.2 := by
    apply Bool.involutive_not.injective
    exact inc.2.2.symm.trans out.2.2
  rw [← hequal] at hopposite
  cases hsign : S.targetSign inc.1.2 <;> simp_all

/-- The source-space input for `C^-`: the image of the compatible incoming
arrow, or zero when no such arrow exists. -/
def lowerBoundarySubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations C.source))) := by
  classical
  exact if h : Nonempty C.IncomingExtension then
      (⊤ : Submodule k (N.obj (Opposite.op
        (obj P.toPresentation.relations (Classical.choice h).1.1)))).map
          (moduleArrowMap N (Classical.choice h).1.2).hom
    else
      ⊥

/-- The source-space input for `C^+`: the kernel of the compatible outgoing
arrow, or the whole source space when no such arrow exists. -/
def upperBoundarySubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations C.source))) := by
  classical
  exact if h : Nonempty C.OutgoingInverseExtension then
      (⊥ : Submodule k (N.obj (Opposite.op
        (obj P.toPresentation.relations (Classical.choice h).1.1)))).comap
          (moduleArrowMap N (Classical.choice h).1.2).hom
    else
      ⊤

/-- Butler--Ringel's lower word subspace `C^-(N)`. -/
def lowerSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u))) :=
  signedPathSubspace N C.path (lowerBoundarySubspace N C)

/-- Butler--Ringel's upper word subspace `C^+(N)`. -/
def upperSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u))) :=
  signedPathSubspace N C.path (upperBoundarySubspace N C)

/-- The boundary image lies in the boundary kernel. -/
theorem lowerBoundarySubspace_le_upperBoundarySubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u t) :
    lowerBoundarySubspace N C ≤ upperBoundarySubspace N C := by
  classical
  by_cases hinc : Nonempty C.IncomingExtension
  · by_cases hout : Nonempty C.OutgoingInverseExtension
    · simp only [lowerBoundarySubspace, upperBoundarySubspace, hinc, hout,
        dite_true]
      let inc := Classical.choice hinc
      let out := Classical.choice hout
      rintro z ⟨w, _, rfl⟩
      change moduleArrowMap N out.1.2 (moduleArrowMap N inc.1.2 w) = 0
      have hzero := C.outgoing_comp_incoming_eq_zero inc out
      have hmorphism :
          moduleArrowMap N inc.1.2 ≫ moduleArrowMap N out.1.2 = 0 := by
        unfold moduleArrowMap
        rw [← Functor.map_comp, ← op_comp, hzero]
        exact N.map_zero _ _
      have happly := congrArg (fun f ↦ f.hom w) hmorphism
      change moduleArrowMap N out.1.2 (moduleArrowMap N inc.1.2 w) = 0
      exact happly.trans (by rfl)
    · simp [upperBoundarySubspace, hout]
  · simp [lowerBoundarySubspace, hinc]

/-- The fundamental Butler--Ringel inclusion `C^-(N) <= C^+(N)`. -/
theorem lowerSubspace_le_upperSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u t) :
    lowerSubspace N C ≤ upperSubspace N C := by
  exact signedPathSubspace_mono N C.path
    (lowerBoundarySubspace_le_upperBoundarySubspace N C)

/-- A module map carries the lower boundary subspace into the corresponding
lower boundary subspace. -/
theorem lowerBoundarySubspace_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u t) :
    (lowerBoundarySubspace M C).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations C.source))).hom ≤
      lowerBoundarySubspace N C := by
  classical
  by_cases hinc : Nonempty C.IncomingExtension
  · simp only [lowerBoundarySubspace, hinc, dite_true]
    let inc := Classical.choice hinc
    rintro z ⟨v, ⟨w, _, rfl⟩, rfl⟩
    refine ⟨f.app (Opposite.op
      (obj P.toPresentation.relations inc.1.1)) w, trivial, ?_⟩
    have hnat := f.naturality
      (BoundQuiver.arrowMap P.toPresentation.relations inc.1.2).op
    have happly := congrArg (fun g ↦ g.hom w) hnat
    simpa only [moduleArrowMap, ModuleCat.comp_apply] using happly.symm
  · simp [lowerBoundarySubspace, hinc]

/-- A module map carries the upper boundary subspace into the corresponding
upper boundary subspace. -/
theorem upperBoundarySubspace_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u t) :
    (upperBoundarySubspace M C).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations C.source))).hom ≤
      upperBoundarySubspace N C := by
  classical
  by_cases hout : Nonempty C.OutgoingInverseExtension
  · simp only [upperBoundarySubspace, hout, dite_true]
    let out := Classical.choice hout
    rintro z ⟨v, hv, rfl⟩
    change moduleArrowMap N out.1.2
      (f.app (Opposite.op
        (obj P.toPresentation.relations C.source)) v) = 0
    have hnat := f.naturality
      (BoundQuiver.arrowMap P.toPresentation.relations out.1.2).op
    have happly := congrArg (fun g ↦ g.hom v) hnat
    have heq :
        f.app (Opposite.op
            (obj P.toPresentation.relations out.1.1))
              (moduleArrowMap M out.1.2 v) =
          moduleArrowMap N out.1.2
            (f.app (Opposite.op
              (obj P.toPresentation.relations C.source)) v) := by
      simpa only [moduleArrowMap, ModuleCat.comp_apply] using happly
    have hvzero : moduleArrowMap M out.1.2 v = 0 := hv
    rw [← heq, hvzero, map_zero]
  · simp [upperBoundarySubspace, hout]

/-- The lower word subspace is natural under arbitrary module morphisms. -/
theorem lowerSubspace_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u t) :
    (lowerSubspace M C).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u))).hom ≤
      lowerSubspace N C := by
  exact (signedPathSubspace_map_le f C.path
    (lowerBoundarySubspace M C)).trans
      (signedPathSubspace_mono N C.path
        (lowerBoundarySubspace_map_le f C))

/-- The upper word subspace is natural under arbitrary module morphisms. -/
theorem upperSubspace_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u t) :
    (upperSubspace M C).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u))).hom ≤
      upperSubspace N C := by
  exact (signedPathSubspace_map_le f C.path
    (upperBoundarySubspace M C)).trans
      (signedPathSubspace_mono N C.path
        (upperBoundarySubspace_map_le f C))

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
