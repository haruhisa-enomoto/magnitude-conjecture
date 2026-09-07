import MagnitudeConjecture.CategoryTheory.QuiverPathCostar
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linear covering functors

This file records the direct-sum Hom-space definition of a covering functor.
For a fixed lift of either endpoint, mapping morphisms and summing over all
lifts of the other endpoint must give a bijection onto the Hom space
downstairs.  This is the categorical covering notion used in the
Bongartz--Gabriel argument; surjectivity on objects is kept as a separate
property.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.LinearCovering

universe u v₁ v₂ w₁ w₂

variable {k : Type u} [Field k]
variable {C : Type v₁} [Category.{w₁} C] [Preadditive C]
variable {D : Type v₂} [Category.{w₂} D] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k]

/-- A bijective linear map remains bijective after passing through a
surjective quotient square, provided that every element which becomes zero
downstairs already becomes zero in the source quotient.  This is the linear
algebra core used to descend covering-functor Hom equivalences through
relation ideals. -/
theorem bijective_of_surjective_quotient_square
    {A A' B B' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module k A] [Module k A'] [Module k B] [Module k B']
    (e : A ≃ₗ[k] B) (qA : A →ₗ[k] A') (qB : B →ₗ[k] B')
    (g : A' →ₗ[k] B')
    (hqA : Function.Surjective qA) (hqB : Function.Surjective qB)
    (hsquare : ∀ a, g (qA a) = qB (e a))
    (hker : ∀ a, qB (e a) = 0 → qA a = 0) :
    Function.Bijective g := by
  constructor
  · intro x y hxy
    have hzero : g (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ := hqA (x - y)
    have hqB : qB (e a) = 0 := by
      rw [← hsquare, ha]
      exact hzero
    have hqA0 := hker a hqB
    rw [ha] at hqA0
    exact sub_eq_zero.mp hqA0
  · intro y
    obtain ⟨b, rfl⟩ := hqB y
    refine ⟨qA (e.symm b), ?_⟩
    rw [hsquare, e.apply_symm_apply]

/-- The objects upstairs mapping literally to a chosen target object. -/
abbrev Fiber (Y : D) := {Z : C // F.obj Z = Y}

/-- Map the summand with fixed source `X` and varying lifted target into the
corresponding Hom space downstairs. -/
def targetFiberHomMap (X : C) (Y : D) :
    DirectSum (Fiber F Y) (fun Z ↦ X ⟶ Z.1) →ₗ[k]
      (F.obj X ⟶ Y) := by
  classical
  exact DirectSum.toModule k (Fiber F Y) _ fun Z ↦
    { toFun := fun f ↦ F.map f ≫ eqToHom Z.2
      map_add' := by
        intro f g
        rw [F.map_add, Preadditive.add_comp]
      map_smul' := by
        intro r f
        rw [F.map_smul, Linear.smul_comp]
        simp }

/-- Map the summand with fixed target `Y` and varying lifted source into the
corresponding Hom space downstairs. -/
def sourceFiberHomMap (X : D) (Y : C) :
    DirectSum (Fiber F X) (fun Z ↦ Z.1 ⟶ Y) →ₗ[k]
      (X ⟶ F.obj Y) := by
  classical
  exact DirectSum.toModule k (Fiber F X) _ fun Z ↦
    { toFun := fun f ↦ eqToHom Z.2.symm ≫ F.map f
      map_add' := by
        intro f g
        rw [F.map_add, Preadditive.comp_add]
      map_smul' := by
        intro r f
        rw [F.map_smul, Linear.comp_smul]
        simp }

/-- Inclusion of one fixed-source lifted Hom space into the target-fibre
direct sum. -/
def targetFiberLof (X : C) (Y : D) (Z : Fiber F Y) :
    (X ⟶ Z.1) →ₗ[k] DirectSum (Fiber F Y) (fun W ↦ X ⟶ W.1) := by
  classical
  exact DirectSum.lof k (Fiber F Y) (fun W ↦ X ⟶ W.1) Z

/-- Inclusion of one fixed-target lifted Hom space into the source-fibre
direct sum. -/
def sourceFiberLof (X : D) (Y : C) (Z : Fiber F X) :
    (Z.1 ⟶ Y) →ₗ[k] DirectSum (Fiber F X) (fun W ↦ W.1 ⟶ Y) := by
  classical
  exact DirectSum.lof k (Fiber F X) (fun W ↦ W.1 ⟶ Y) Z

/-- Precompose every fixed-target-fibre summand by one morphism upstairs. -/
def targetFiberPrecomp (Y : D) {X' X : C} (e : X' ⟶ X) :
    DirectSum (Fiber F Y) (fun W ↦ X ⟶ W.1) →ₗ[k]
      DirectSum (Fiber F Y) (fun W ↦ X' ⟶ W.1) := by
  classical
  exact DirectSum.toModule k (Fiber F Y) _ fun W ↦ by
    let pre : (X ⟶ W.1) →ₗ[k] (X' ⟶ W.1) :=
      { toFun := fun f ↦ e ≫ f
        map_add' := by
          intro f g
          rw [Preadditive.comp_add]
        map_smul' := by
          intro r f
          exact CategoryTheory.Linear.comp_smul _ _ _ e r f }
    exact
      (DirectSum.lof k (Fiber F Y) (fun V ↦ X' ⟶ V.1) W).comp pre

/-- Postcompose every fixed-source-fibre summand by one morphism upstairs. -/
def sourceFiberPostcomp (X : D) {Y Z : C} (e : Y ⟶ Z) :
    DirectSum (Fiber F X) (fun W ↦ W.1 ⟶ Y) →ₗ[k]
      DirectSum (Fiber F X) (fun W ↦ W.1 ⟶ Z) := by
  classical
  exact DirectSum.toModule k (Fiber F X) _ fun W ↦ by
    let post : (W.1 ⟶ Y) →ₗ[k] (W.1 ⟶ Z) :=
      { toFun := fun f ↦ f ≫ e
        map_add' := by
          intro f g
          rw [Preadditive.add_comp]
        map_smul' := by
          intro r f
          exact CategoryTheory.Linear.smul_comp _ _ _ r f e }
    exact
      (DirectSum.lof k (Fiber F X) (fun V ↦ V.1 ⟶ Z) W).comp post

@[simp]
theorem targetFiberHomMap_lof (X : C) (Y : D)
    (Z : Fiber F Y) (f : X ⟶ Z.1) :
    targetFiberHomMap (k := k) F X Y
        (targetFiberLof (k := k) F X Y Z f) =
      F.map f ≫ eqToHom Z.2 := by
  classical
  simp [targetFiberHomMap, targetFiberLof]

@[simp]
theorem sourceFiberHomMap_lof (X : D) (Y : C)
    (Z : Fiber F X) (f : Z.1 ⟶ Y) :
    sourceFiberHomMap (k := k) F X Y
        (sourceFiberLof (k := k) F X Y Z f) =
      eqToHom Z.2.symm ≫ F.map f := by
  classical
  simp [sourceFiberHomMap, sourceFiberLof]

omit [Preadditive D] [CategoryTheory.Linear k D] [F.Additive] [F.Linear k] in
@[simp]
theorem targetFiberPrecomp_lof (Y : D) {X' X : C} (e : X' ⟶ X)
    (W : Fiber F Y) (f : X ⟶ W.1) :
    targetFiberPrecomp (k := k) F Y e
        (targetFiberLof (k := k) F X Y W f) =
      targetFiberLof (k := k) F X' Y W (e ≫ f) := by
  classical
  simp [targetFiberPrecomp, targetFiberLof]

omit [Preadditive D] [CategoryTheory.Linear k D] [F.Additive] [F.Linear k] in
/-- Precomposition in a target fibre acts componentwise. -/
@[simp]
theorem targetFiberPrecomp_apply (Y : D) {X' X : C} (e : X' ⟶ X)
    (a : DirectSum (Fiber F Y) (fun W ↦ X ⟶ W.1))
    (V : Fiber F Y) :
    targetFiberPrecomp (k := k) F Y e a V = e ≫ a V := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of W f =>
      rw [← DirectSum.lof_eq_of k (Fiber F Y) (fun U ↦ X ⟶ U.1) W f]
      change
        (targetFiberPrecomp (k := k) F Y e
          (targetFiberLof (k := k) F X Y W f)) V =
        e ≫ (targetFiberLof (k := k) F X Y W f) V
      rw [targetFiberPrecomp_lof]
      by_cases hWV : W = V
      · subst W
        simp [targetFiberLof]
      · simp [targetFiberLof, DirectSum.lof_eq_of,
          DirectSum.of_apply, hWV]
  | add a b ha hb =>
      simp only [map_add, DirectSum.add_apply, ha, hb,
        Preadditive.comp_add]

omit [Preadditive D] [CategoryTheory.Linear k D] [F.Additive] [F.Linear k] in
@[simp]
theorem sourceFiberPostcomp_lof (X : D) {Y Z : C} (e : Y ⟶ Z)
    (W : Fiber F X) (f : W.1 ⟶ Y) :
    sourceFiberPostcomp (k := k) F X e
        (sourceFiberLof (k := k) F X Y W f) =
      sourceFiberLof (k := k) F X Z W (f ≫ e) := by
  classical
  simp [sourceFiberPostcomp, sourceFiberLof]

omit [Preadditive D] [CategoryTheory.Linear k D] [F.Additive] [F.Linear k] in
/-- Postcomposition in a source fibre acts componentwise. -/
@[simp]
theorem sourceFiberPostcomp_apply (X : D) {Y Z : C} (e : Y ⟶ Z)
    (a : DirectSum (Fiber F X) (fun W ↦ W.1 ⟶ Y))
    (V : Fiber F X) :
    sourceFiberPostcomp (k := k) F X e a V = a V ≫ e := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of W f =>
      rw [← DirectSum.lof_eq_of k (Fiber F X) (fun U ↦ U.1 ⟶ Y) W f]
      change
        (sourceFiberPostcomp (k := k) F X e
          (sourceFiberLof (k := k) F X Y W f)) V =
        (sourceFiberLof (k := k) F X Y W f) V ≫ e
      rw [sourceFiberPostcomp_lof]
      by_cases hWV : W = V
      · subst W
        simp [sourceFiberLof]
      · simp [sourceFiberLof, DirectSum.lof_eq_of,
          DirectSum.of_apply, hWV]
  | add a b ha hb =>
      simp only [map_add, DirectSum.add_apply, ha, hb,
        Preadditive.add_comp]

/-- The fixed-source fibre map intertwines precomposition upstairs with
precomposition by the mapped morphism downstairs. -/
theorem targetFiberHomMap_targetFiberPrecomp
    (Y : D) {X' X : C} (e : X' ⟶ X)
    (a : DirectSum (Fiber F Y) (fun W ↦ X ⟶ W.1)) :
    targetFiberHomMap (k := k) F X' Y
        (targetFiberPrecomp (k := k) F Y e a) =
      F.map e ≫ targetFiberHomMap (k := k) F X Y a := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of W f =>
      rw [← DirectSum.lof_eq_of k (Fiber F Y)
        (fun V ↦ X ⟶ V.1) W f]
      change
        targetFiberHomMap (k := k) F X' Y
            (targetFiberPrecomp (k := k) F Y e
              (targetFiberLof (k := k) F X Y W f)) =
          F.map e ≫ targetFiberHomMap (k := k) F X Y
              (targetFiberLof (k := k) F X Y W f)
      rw [targetFiberPrecomp_lof, targetFiberHomMap_lof,
        targetFiberHomMap_lof, F.map_comp]
      simp only [Category.assoc]
  | add a b ha hb =>
      simp only [map_add, ha, hb, Preadditive.comp_add]

/-- The fixed-target fibre map intertwines postcomposition upstairs with
postcomposition by the mapped morphism downstairs. -/
theorem sourceFiberHomMap_sourceFiberPostcomp
    (X : D) {Y Z : C} (e : Y ⟶ Z)
    (a : DirectSum (Fiber F X) (fun W ↦ W.1 ⟶ Y)) :
    sourceFiberHomMap (k := k) F X Z
        (sourceFiberPostcomp (k := k) F X e a) =
      sourceFiberHomMap (k := k) F X Y a ≫ F.map e := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of W f =>
      rw [← DirectSum.lof_eq_of k (Fiber F X)
        (fun V ↦ V.1 ⟶ Y) W f]
      change
        sourceFiberHomMap (k := k) F X Z
            (sourceFiberPostcomp (k := k) F X e
              (sourceFiberLof (k := k) F X Y W f)) =
          sourceFiberHomMap (k := k) F X Y
              (sourceFiberLof (k := k) F X Y W f) ≫ F.map e
      rw [sourceFiberPostcomp_lof, sourceFiberHomMap_lof,
        sourceFiberHomMap_lof, F.map_comp]
      simp only [Category.assoc]
  | add a b ha hb =>
      simp only [map_add, ha, hb, Preadditive.add_comp]

omit [Preadditive D] [CategoryTheory.Linear k D] [F.Additive] [F.Linear k] in
/-- Successive postcomposition of a source-fibre family is postcomposition
by the composite upstairs. -/
theorem sourceFiberPostcomp_comp
    (X : D) {Y Z W : C} (e : Y ⟶ Z) (f : Z ⟶ W)
    (a : DirectSum (Fiber F X) (fun V ↦ V.1 ⟶ Y)) :
    sourceFiberPostcomp (k := k) F X f
        (sourceFiberPostcomp (k := k) F X e a) =
      sourceFiberPostcomp (k := k) F X (e ≫ f) a := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of V g =>
      rw [← DirectSum.lof_eq_of k (Fiber F X)
        (fun U ↦ U.1 ⟶ Y) V g]
      change sourceFiberPostcomp (k := k) F X f
          (sourceFiberPostcomp (k := k) F X e
            (sourceFiberLof (k := k) F X Y V g)) =
        sourceFiberPostcomp (k := k) F X (e ≫ f)
          (sourceFiberLof (k := k) F X Y V g)
      rw [sourceFiberPostcomp_lof, sourceFiberPostcomp_lof,
        sourceFiberPostcomp_lof, Category.assoc]
  | add a b ha hb =>
      simp only [map_add, ha, hb]

omit [Preadditive D] [CategoryTheory.Linear k D] [F.Additive] [F.Linear k] in
/-- Successive precomposition of a target-fibre family is precomposition by
the composite upstairs. -/
theorem targetFiberPrecomp_comp
    (Y : D) {X'' X' X : C} (e : X'' ⟶ X') (f : X' ⟶ X)
    (a : DirectSum (Fiber F Y) (fun V ↦ X ⟶ V.1)) :
    targetFiberPrecomp (k := k) F Y e
        (targetFiberPrecomp (k := k) F Y f a) =
      targetFiberPrecomp (k := k) F Y (e ≫ f) a := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of V g =>
      rw [← DirectSum.lof_eq_of k (Fiber F Y)
        (fun U ↦ X ⟶ U.1) V g]
      change targetFiberPrecomp (k := k) F Y e
          (targetFiberPrecomp (k := k) F Y f
            (targetFiberLof (k := k) F X Y V g)) =
        targetFiberPrecomp (k := k) F Y (e ≫ f)
          (targetFiberLof (k := k) F X Y V g)
      rw [targetFiberPrecomp_lof, targetFiberPrecomp_lof,
        targetFiberPrecomp_lof, Category.assoc]
  | add a b ha hb =>
      simp only [map_add, ha, hb]

/-- A linear covering functor: after fixing either lifted endpoint, the Hom
space downstairs is the direct sum of the Hom spaces over all lifts of the
other endpoint. -/
structure IsCovering : Prop where
  target_bijective : ∀ (X : C) (Y : D),
    Function.Bijective (targetFiberHomMap (k := k) F X Y)
  source_bijective : ∀ (X : D) (Y : C),
    Function.Bijective (sourceFiberHomMap (k := k) F X Y)

namespace IsCovering

variable {F}

/-- The fixed-source direct-sum Hom equivalence supplied by a covering
functor. -/
def targetFiberHomLinearEquiv (hF : IsCovering (k := k) F)
    (X : C) (Y : D) :
    DirectSum (Fiber F Y) (fun Z ↦ X ⟶ Z.1) ≃ₗ[k]
      (F.obj X ⟶ Y) :=
  LinearEquiv.ofBijective (targetFiberHomMap (k := k) F X Y)
    (hF.target_bijective X Y)

/-- The fixed-target direct-sum Hom equivalence supplied by a covering
functor. -/
def sourceFiberHomLinearEquiv (hF : IsCovering (k := k) F)
    (X : D) (Y : C) :
    DirectSum (Fiber F X) (fun Z ↦ Z.1 ⟶ Y) ≃ₗ[k]
      (X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective (sourceFiberHomMap (k := k) F X Y)
    (hF.source_bijective X Y)

@[simp]
theorem targetFiberHomLinearEquiv_apply (hF : IsCovering (k := k) F)
    (X : C) (Y : D)
    (f : DirectSum (Fiber F Y) (fun Z ↦ X ⟶ Z.1)) :
    hF.targetFiberHomLinearEquiv X Y f =
      targetFiberHomMap (k := k) F X Y f :=
  rfl

@[simp]
theorem sourceFiberHomLinearEquiv_apply (hF : IsCovering (k := k) F)
    (X : D) (Y : C)
    (f : DirectSum (Fiber F X) (fun Z ↦ Z.1 ⟶ Y)) :
    hF.sourceFiberHomLinearEquiv X Y f =
      sourceFiberHomMap (k := k) F X Y f :=
  rfl

/-- Every linear covering functor is faithful: an individual Hom space is
one summand of either covering decomposition. -/
theorem map_injective (hF : IsCovering (k := k) F) (X Y : C) :
    Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  classical
  let Z : Fiber F (F.obj X) := ⟨X, rfl⟩
  intro f g hfg
  have hlof :
      sourceFiberLof (k := k) F (F.obj X) Y Z f =
        sourceFiberLof (k := k) F (F.obj X) Y Z g := by
    apply (hF.sourceFiberHomLinearEquiv (F.obj X) Y).injective
    rw [sourceFiberHomLinearEquiv_apply, sourceFiberHomLinearEquiv_apply,
      sourceFiberHomMap_lof, sourceFiberHomMap_lof]
    simpa using hfg
  have hcomponent := congrArg
    (DirectSum.component k (Fiber F (F.obj X))
      (fun W ↦ W.1 ⟶ Y) Z) hlof
  simpa [sourceFiberLof] using hcomponent

/-- The faithful structure carried by a linear covering functor. -/
theorem faithful (hF : IsCovering (k := k) F) : F.Faithful where
  map_injective := fun {_ _} _ _ h ↦ hF.map_injective _ _ h

/-- A covering functor which is injective on objects is fully faithful.

Indeed, the fibre over `F.obj Y` then consists only of `Y`, so the
fixed-source covering isomorphism is just the ordinary map on the Hom space
`X ⟶ Y`. -/
theorem map_bijective_of_obj_injective (hF : IsCovering (k := k) F)
    (hobj : Function.Injective F.obj) (X Y : C) :
    Function.Bijective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  classical
  let Z : Fiber F (F.obj Y) := ⟨Y, rfl⟩
  have hZ : Function.Bijective
      (targetFiberLof (k := k) F X (F.obj Y) Z) := by
    constructor
    · intro f g hfg
      have := congrArg
        (DirectSum.component k (Fiber F (F.obj Y))
          (fun W ↦ X ⟶ W.1) Z) hfg
      simpa [targetFiberLof] using this
    · intro f
      refine ⟨DirectSum.component k (Fiber F (F.obj Y))
        (fun W ↦ X ⟶ W.1) Z f, ?_⟩
      apply DirectSum.ext_component k
      intro W
      have hW : W = Z := Subtype.ext (hobj W.2)
      subst W
      simp [targetFiberLof]
  have hcomp := (hF.target_bijective X (F.obj Y)).comp hZ
  have heq :
      (targetFiberHomMap (k := k) F X (F.obj Y)) ∘
          (targetFiberLof (k := k) F X (F.obj Y) Z) =
        (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
    funext f
    simpa [Z] using targetFiberHomMap_lof (k := k) F X (F.obj Y) Z f
  rw [heq] at hcomp
  exact hcomp

/-- A covering functor which is injective on objects, packaged as a fully
faithful functor. -/
noncomputable def fullyFaithfulOfObjInjective
    (hF : IsCovering (k := k) F) (hobj : Function.Injective F.obj) :
    F.FullyFaithful := by
  letI : F.Faithful :=
    ⟨fun h ↦ (hF.map_bijective_of_obj_injective hobj _ _).injective h⟩
  letI : F.Full :=
    ⟨(hF.map_bijective_of_obj_injective hobj _ _).surjective⟩
  exact Functor.FullyFaithful.ofFullyFaithful F

/-- A covering functor which is bijective on objects is an equivalence of
categories. -/
theorem isEquivalenceOfObjBijective (hF : IsCovering (k := k) F)
    (hobj : Function.Bijective F.obj) : F.IsEquivalence := by
  let hff := hF.fullyFaithfulOfObjInjective hobj.injective
  exact
    { faithful := hff.faithful
      full := hff.full
      essSurj := F.essSurj_of_surj hobj.surjective }

end IsCovering

end MagnitudeConjecture.LinearCovering
