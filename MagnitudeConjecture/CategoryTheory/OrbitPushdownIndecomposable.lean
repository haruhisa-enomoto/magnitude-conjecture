import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd
import MagnitudeConjecture.CategoryTheory.OrbitPullupPushdownDiagonalInvariance
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Indecomposability of orbit push-down

The invariant-summand argument implies that an orbit push-down is
indecomposable when the upstairs module has local endomorphism ring and trivial
translate stabilizer.  Localness passes to every translate by precomposition
with the shift autoequivalences, while trivial stabilizer makes the translates
pairwise nonisomorphic.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

variable (M : C ⥤ ModuleCat.{w} k)
variable [M.Additive] [M.Linear k]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- Trivial translate stabilizer makes the full family of translates pairwise
nonisomorphic. -/
theorem orbitPullupPushdownTranslate_pairwise_noniso_of_trivial_stabilizer
    (htrivial : ∀ a : A,
      Nonempty (M ≅ shiftFunctor C a ⋙ M) → a = 0)
    (b c : A) (hbc : b ≠ c) :
    ¬ Nonempty
      (orbitPullupPushdownTranslate (A := A) M b ≅
        orbitPullupPushdownTranslate (A := A) M c) := by
  rintro ⟨e⟩
  let eshift := Functor.isoWhiskerLeft (shiftFunctor C (-b)) e
  let eleft : shiftFunctor C (-b) ⋙ (shiftFunctor C b ⋙ M) ≅ M :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (shiftFunctorCompIsoId C (-b) b (neg_add_cancel b)) M ≪≫
      Functor.leftUnitor M
  let eright : shiftFunctor C (-b) ⋙ (shiftFunctor C c ⋙ M) ≅
      shiftFunctor C (-b + c) ⋙ M :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (shiftFunctorAdd C (-b) c).symm M
  have hzero : -b + c = 0 := htrivial (-b + c)
    ⟨eleft.symm ≪≫ eshift ≪≫ eright⟩
  apply hbc
  have := congrArg (b + ·) hzero
  symm
  simpa [add_assoc] using this

/-- Precomposition by a deck shift identifies the endomorphism rings of a
module and its translate. -/
noncomputable def orbitPullupPushdownTranslateEndRingEquiv (b : A) :
    End M ≃+* End (orbitPullupPushdownTranslate (A := A) M b) := by
  let W : (C ⥤ ModuleCat.{w} k) ⥤ (C ⥤ ModuleCat.{w} k) :=
    (Functor.whiskeringLeft C C (ModuleCat.{w} k)).obj
      (shiftFunctor C b)
  change End M ≃+* End (W.obj M)
  letI : W.IsEquivalence := inferInstance
  exact
    { toFun := W.map
      invFun := W.preimage
      left_inv := W.preimage_map
      right_inv := W.map_preimage
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun f g ↦ W.map_comp g f }

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- A local endomorphism ring passes from a module to every translate. -/
theorem orbitPullupPushdownTranslate_end_isLocalRing
    (hlocal : IsLocalRing (End M)) (b : A) :
    IsLocalRing
      (End (orbitPullupPushdownTranslate (A := A) M b)) := by
  letI : IsLocalRing (End M) := hlocal
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (orbitPullupPushdownTranslateEndRingEquiv (A := A) M b)

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- Every translate of a module with local endomorphism ring is
indecomposable. -/
theorem orbitPullupPushdownTranslate_indecomposable_of_local_end
    (hlocal : IsLocalRing (End M)) (b : A) :
    Indecomposable (orbitPullupPushdownTranslate (A := A) M b) := by
  letI : IsLocalRing
      (End (orbitPullupPushdownTranslate (A := A) M b)) :=
    orbitPullupPushdownTranslate_end_isLocalRing (A := A) M hlocal b
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _

/-- If the translates form a pairwise nonisomorphic Krull--Schmidt family,
the orbit push-down of `M` is indecomposable. -/
theorem orbitPushdown_indecomposable
    (hindecomp : ∀ b : A,
      Indecomposable (orbitPullupPushdownTranslate (A := A) M b))
    (hlocal : ∀ b : A,
      IsLocalRing (End
        (orbitPullupPushdownTranslate (A := A) M b)))
    (hpair : ∀ b c : A, b ≠ c →
      ¬ Nonempty
        (orbitPullupPushdownTranslate (A := A) M b ≅
          orbitPullupPushdownTranslate (A := A) M c)) :
    Indecomposable (orbitPushdown (A := A) M) := by
  constructor
  · intro hzero
    have hzeroRestriction : IsZero
        (ShiftOrbitCategory.identityComponentFunctor ⋙
          orbitPushdown (A := A) M) := by
      exact Functor.map_isZero
        ((Functor.whiskeringLeft C (ShiftOrbitCategory C A)
          (ModuleCat.{w} k)).obj
            ShiftOrbitCategory.identityComponentFunctor) hzero
    have hzeroPullup : IsZero (orbitPullupPushdown (A := A) M) :=
      IsZero.of_iso hzeroRestriction
        (orbitPullupPushdownIso (A := A) M).symm
    apply (hindecomp 0).1
    rw [IsZero.iff_id_eq_zero]
    rw [← orbitPullupPushdownTranslateLof_component_self
      (A := A) M 0]
    have hlof : orbitPullupPushdownTranslateLof (A := A) M 0 = 0 :=
      hzeroPullup.eq_of_tgt _ _
    rw [hlof, zero_comp]
  · intro L Q e
    let j : L ⟶ orbitPushdown (A := A) M := biprod.inl ≫ e.inv
    let r : orbitPushdown (A := A) M ⟶ L := e.hom ≫ biprod.fst
    let j' : Q ⟶ orbitPushdown (A := A) M := biprod.inr ≫ e.inv
    let r' : orbitPushdown (A := A) M ⟶ Q := e.hom ≫ biprod.snd
    have hjr : j ≫ r = 𝟙 L := by
      simp [j, r, Category.assoc]
    have hj'r' : j' ≫ r' = 𝟙 Q := by
      simp [j', r', Category.assoc]
    have htotal : r ≫ j + r' ≫ j' =
        𝟙 (orbitPushdown (A := A) M) := by
      calc
        r ≫ j + r' ≫ j' =
            e.hom ≫ (biprod.fst ≫ biprod.inl +
              biprod.snd ≫ biprod.inr) ≫ e.inv := by
                dsimp [r, j, r', j']
                simp only [Preadditive.comp_add, Preadditive.add_comp,
                  Category.assoc]
        _ = 𝟙 _ := by simp
    rcases orbitPushdown_one_retract_inclusion_isIso
      (A := A) M j r hjr j' r' hj'r' htotal
        hindecomp hlocal hpair with hj | hj'
    · right
      letI : IsIso j := hj
      have hrj : r ≫ j = 𝟙 _ := by
        apply (cancel_epi j).1
        simp [← Category.assoc, hjr]
      have hr'j' : r' ≫ j' = 0 := by
        have h : 𝟙 _ + (r' ≫ j') = 𝟙 _ + 0 := by
          simpa [hrj] using htotal
        exact add_left_cancel h
      rw [IsZero.iff_id_eq_zero]
      have h := congrArg (fun f ↦ j' ≫ f ≫ r') hr'j'
      simpa [Category.assoc, hj'r'] using h
    · left
      letI : IsIso j' := hj'
      have hr'j' : r' ≫ j' = 𝟙 _ := by
        apply (cancel_epi j').1
        simp [← Category.assoc, hj'r']
      have hrj : r ≫ j = 0 := by
        have h : (r ≫ j) + 𝟙 _ = 0 + 𝟙 _ := by
          simpa [hr'j'] using htotal
        exact add_right_cancel h
      rw [IsZero.iff_id_eq_zero]
      have h := congrArg (fun f ↦ j ≫ f ≫ r) hrj
      simpa [Category.assoc, hjr] using h

/-- Gabriel's invariant-summand conclusion: a module with local endomorphism
ring and trivial translate stabilizer has indecomposable orbit push-down. -/
theorem orbitPushdown_indecomposable_of_local_end_of_trivial_stabilizer
    (hlocal : IsLocalRing (End M))
    (htrivial : ∀ a : A,
      Nonempty (M ≅ shiftFunctor C a ⋙ M) → a = 0) :
    Indecomposable (orbitPushdown (A := A) M) := by
  apply orbitPushdown_indecomposable (A := A) M
  · exact orbitPullupPushdownTranslate_indecomposable_of_local_end
      (A := A) M hlocal
  · exact orbitPullupPushdownTranslate_end_isLocalRing
      (A := A) M hlocal
  · exact orbitPullupPushdownTranslate_pairwise_noniso_of_trivial_stabilizer
      (A := A) M htrivial

end MagnitudeConjecture.CoveringHom
