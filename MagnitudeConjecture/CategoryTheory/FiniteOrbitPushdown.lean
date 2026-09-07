import MagnitudeConjecture.CategoryTheory.DeckOrbitSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Finite-dimensional Gabriel push-down on an orbit skeleton

A finite-support module upstairs has only finitely many nonzero translated
values at a fixed object when the deck action is free.  The corresponding
direct sum is therefore finite-dimensional.  After passing to one chosen
representative per deck orbit, the object support of push-down is contained
in the quotient image of the finite upstairs support.

These two facts restrict the generic skeletal Gabriel push-down functor to
the finite-dimensional module categories used by the covering argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

section FiniteDirectSum

variable {k : Type uK} [Field k]
variable {ι : Type u} (V : ι → Type uM)
variable [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- A direct sum is finite-dimensional when only finitely many of its
summands are nontrivial and every summand is finite-dimensional. -/
theorem finiteDimensional_directSum_of_finite_nontrivial
    [∀ i, FiniteDimensional k (V i)]
    (h : {i : ι | Nontrivial (V i)}.Finite) :
    FiniteDimensional k (DirectSum ι V) := by
  classical
  let S : Set ι := {i | Nontrivial (V i)}
  letI : Fintype S := h.fintype
  let p : DirectSum S (fun i ↦ V i.1) →ₗ[k] DirectSum ι V :=
    DirectSum.toModule k S (DirectSum ι V) fun i ↦
      DirectSum.lof k ι V i.1
  apply Module.Finite.of_surjective p
  intro x
  induction x using DirectSum.induction_on with
  | zero =>
      exact ⟨0, p.map_zero⟩
  | of i x =>
      by_cases hi : Nontrivial (V i)
      · let j : S := ⟨i, hi⟩
        exact ⟨DirectSum.lof k S (fun j ↦ V j.1) j x, by
          change p (DirectSum.lof k S (fun j ↦ V j.1) j x) =
            DirectSum.lof k ι V i x
          rw [DirectSum.toModule_lof]⟩
      · letI : Subsingleton (V i) :=
          not_nontrivial_iff_subsingleton.mp hi
        exact ⟨0, by simp [Subsingleton.elim x 0]⟩
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by simp [hx', hy']⟩

/-- A nontrivial direct sum has a nontrivial summand. -/
theorem exists_nontrivial_of_directSum_nontrivial
    (h : Nontrivial (DirectSum ι V)) :
    ∃ i : ι, Nontrivial (V i) := by
  by_contra hn
  have hsub : ∀ i, Subsingleton (V i) := by
    intro i
    rw [← not_nontrivial_iff_subsingleton]
    intro hi
    exact hn ⟨i, hi⟩
  letI : ∀ i, Subsingleton (V i) := hsub
  exact not_nontrivial (DirectSum ι V) h

/-- A direct sum is subsingleton exactly when every summand is
subsingleton. -/
theorem subsingleton_directSum_iff :
    Subsingleton (DirectSum ι V) ↔ ∀ i, Subsingleton (V i) := by
  classical
  constructor
  · intro h i
    letI : Subsingleton (DirectSum ι V) := h
    constructor
    intro x y
    exact DirectSum.of_injective i (Subsingleton.elim
      (DirectSum.of V i x) (DirectSum.of V i y))
  · intro h
    letI (i : ι) : Subsingleton (V i) := h i
    infer_instance

end FiniteDirectSum

namespace CoherentDeckShift

variable {k : Type uK} [Field k]

section FreeAction

variable {C : Type u}
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- Freeness of the strict deck action makes inverse translates of a fixed
object injectively indexed by the additive shift group. -/
theorem inverseTranslate_injective (X : C) :
    Function.Injective (fun b : Additive G ↦ b.toMul⁻¹ • X) := by
  intro a b h
  apply Additive.toMul.injective
  apply inv_injective
  exact IsCancelSMul.right_cancel _ _ X h

end FreeAction

section Finiteness

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]
variable (M : FiniteDimensionalModuleCategory (C := C) k)

omit [IsCancelSMul G C]
  [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k] in
/-- A shifted value is nonzero exactly when the corresponding inverse deck
translate belongs to the upstairs object support. -/
theorem nontrivial_shift_value_iff (b : Additive G) (X : C) :
    letI := D.hasShift
    Nontrivial
        (M.obj.obj.obj ((shiftFunctor C b).obj X)) ↔
      b.toMul⁻¹ • X ∈ moduleSupport k M.obj.obj := by
  letI := D.hasShift
  change Nontrivial
      (M.obj.obj.obj ((D.core.F b).obj X)) ↔
    Nontrivial (M.obj.obj.obj (b.toMul⁻¹ • X))
  simpa using
    (M.obj.obj.mapIso
      (D.objIso b.toMul X)).toLinearEquiv.toEquiv.nontrivial_congr

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k] in
/-- At a fixed downstairs orbit, only finitely many translated summands of
an upstairs finite-support module are nonzero. -/
theorem finite_nontrivial_shift_values (X : C) :
    letI := D.hasShift
    {b : Additive G |
      Nontrivial (M.obj.obj.obj ((shiftFunctor C b).obj X))}.Finite := by
  letI := D.hasShift
  have hset :
      {b : Additive G |
        Nontrivial (M.obj.obj.obj ((shiftFunctor C b).obj X))} =
        (fun b : Additive G ↦ b.toMul⁻¹ • X) ⁻¹'
          moduleSupport k M.obj.obj := by
    ext b
    exact D.nontrivial_shift_value_iff (k := k) M b X
  rw [hset]
  exact (finite_moduleSupport k M).preimage
    (inverseTranslate_injective (G := G) X).injOn

/-- Restriction to an orbit representative makes every push-down value
finite-dimensional. -/
theorem orbitSkeletonPushdown_pointwise_finite
    (q : letI := D.hasShift
      letI := D.additiveShift
      DeckOrbitSkeleton C G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    FiniteDimensional k
      ((orbitSkeletonPushdown (G := G) M.obj.obj).obj q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let X : C := deckOrbitRepresentative
    (show MulAction.orbitRel.Quotient G C from q)
  change FiniteDimensional k
    (DirectSum (Additive G) fun b ↦
      M.obj.obj.obj ((shiftFunctor C b).obj X))
  letI : ∀ b : Additive G, FiniteDimensional k
      (M.obj.obj.obj ((shiftFunctor C b).obj X)) :=
    fun b ↦ M.property.1 ((shiftFunctor C b).obj X)
  exact finiteDimensional_directSum_of_finite_nontrivial
    (fun b : Additive G ↦
      M.obj.obj.obj ((shiftFunctor C b).obj X))
    (D.finite_nontrivial_shift_values (k := k) M X)

omit [IsCancelSMul G C] in
/-- A skeletal push-down value is zero exactly when every translated
upstairs value over that orbit is zero. -/
theorem orbitSkeletonPushdown_obj_isZero_iff
    (q : letI := D.hasShift
      letI := D.additiveShift
      DeckOrbitSkeleton C G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    IsZero ((orbitSkeletonPushdown (G := G) M.obj.obj).obj q) ↔
      ∀ b : Additive G,
        IsZero (M.obj.obj.obj
          ((shiftFunctor C b).obj
            (deckOrbitRepresentative
              (show MulAction.orbitRel.Quotient G C from q)))) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton
      (DirectSum (Additive G) fun b ↦
        M.obj.obj.obj ((shiftFunctor C b).obj
          (deckOrbitRepresentative
            (show MulAction.orbitRel.Quotient G C from q)))) ↔ _
  rw [subsingleton_directSum_iff]
  exact ⟨fun h b ↦ ModuleCat.isZero_iff_subsingleton.mpr (h b),
    fun h b ↦ ModuleCat.isZero_iff_subsingleton.mp (h b)⟩

omit [IsCancelSMul G C] in
/-- The support of skeletal push-down is contained in the quotient image of
the finite upstairs support. -/
theorem moduleSupport_orbitSkeletonPushdown_subset :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    moduleSupport k (orbitSkeletonPushdown (G := G) M.obj.obj) ⊆
      Quotient.mk'' '' moduleSupport k M.obj.obj := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  intro q hq
  let X : C := deckOrbitRepresentative
    (show MulAction.orbitRel.Quotient G C from q)
  change Nontrivial
    (DirectSum (Additive G) fun b ↦
      M.obj.obj.obj ((shiftFunctor C b).obj X)) at hq
  obtain ⟨b, hb⟩ :=
    exists_nontrivial_of_directSum_nontrivial
      (fun b : Additive G ↦
        M.obj.obj.obj ((shiftFunctor C b).obj X)) hq
  refine ⟨b.toMul⁻¹ • X,
    (D.nontrivial_shift_value_iff (k := k) M b X).mp hb, ?_⟩
  calc
    Quotient.mk'' (b.toMul⁻¹ • X) = Quotient.mk'' X :=
      Quotient.sound (MulAction.mem_orbit X b.toMul⁻¹)
    _ = q := deckOrbitRepresentative_mk
      (show MulAction.orbitRel.Quotient G C from q)

omit [IsCancelSMul G C] in
/-- Skeletal push-down has finite literal object support. -/
theorem orbitSkeletonPushdown_finite_support :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (moduleSupport k
      (orbitSkeletonPushdown (G := G) M.obj.obj)).Finite := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact ((finite_moduleSupport k M).image Quotient.mk'').subset
    (D.moduleSupport_orbitSkeletonPushdown_subset (k := k) M)

/-- Skeletal push-down of a finite-dimensional upstairs module satisfies the
downstairs pointwise and finite-support conditions. -/
theorem orbitSkeletonPushdown_isFiniteDimensionalModule :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    IsFiniteDimensionalModule k
      ((linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).obj M.obj) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  constructor
  · intro q
    exact D.orbitSkeletonPushdown_pointwise_finite (k := k) M q
  · exact D.orbitSkeletonPushdown_finite_support (k := k) M

/-- Gabriel push-down from finite-dimensional upstairs modules to
finite-dimensional modules on the one-representative-per-orbit base. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdown :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (IsFiniteDimensionalModule
    (C := DeckOrbitSkeleton C G) k).lift
      ((IsFiniteDimensionalModule (C := C) k).ι ⋙
        linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G))
      (D.orbitSkeletonPushdown_isFiniteDimensionalModule (k := k))

/-- View the finite skeletal push-down through an extensionally chosen shift
instance known to equal the coherent deck shift.  Keeping the equality
explicit prevents downstream orbit-category types from forcing Lean to
normalize two large but equal shift constructions. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift) :
    letI := H
    letI := hadd
    letI := hlinear
    FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  exact D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)

/-- The transported finite push-down has the expected underlying linear
module object for the chosen shift instance. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_obj_obj
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := H
    letI := hadd
    letI := hlinear
    ((D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
      (k := k) H hadd hlinear hH).obj M).obj =
      (linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).obj M.obj := by
  cases hH
  rfl

/-- Lift an isomorphism from the expected underlying push-down module through
the transported finite-dimensional full subcategory. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_isoMk
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := H
    letI := hadd
    letI := hlinear
    ∀ {Y : FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k},
      ((linearModuleOrbitSkeletonPushdown
          (k := k) (C := C) (G := G)).obj M.obj ≅ Y.obj) →
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
          (k := k) H hadd hlinear hH).obj M ≅ Y) := by
  letI := H
  letI := hadd
  letI := hlinear
  intro Y e
  exact ObjectProperty.isoMk _
    (eqToIso
      (D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_obj_obj
        (k := k) H hadd hlinear hH M) ≪≫ e)

instance finiteDimensionalModuleOrbitSkeletonPushdown_additive :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp [finiteDimensionalModuleOrbitSkeletonPushdown]
  infer_instance

/-- Additivity of finite push-down transported across an explicit equality of
shift instances. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_additive
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
      (k := k) H hadd hlinear hH).Additive := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  change (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).Additive
  infer_instance

instance finiteDimensionalModuleOrbitSkeletonPushdown_linear :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := (IsFiniteDimensionalModule (C := C) k).ι ⋙
    linearModuleOrbitSkeletonPushdown (k := k) (C := C) (G := G)
  constructor
  intro X Y f r
  apply ObjectProperty.hom_ext
  change F.map (r • f) = r • F.map f
  exact F.map_smul r f

end Finiteness

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
