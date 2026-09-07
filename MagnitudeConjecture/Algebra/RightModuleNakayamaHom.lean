import MagnitudeConjecture.Algebra.RightModuleNakayama

/-!
# The finite-projective Nakayama--Hom pairing for right modules

This file develops the concrete comparison

`Hom_B(Y, D Hom_B(P,B)) \simeq D Hom_B(P,Y)`

for a finitely generated projective right module `P`.  It is the duality
input for identifying the Nakayama kernel of a minimal presentation with
the Auslander--Reiten translate.  The proof uses only the finite frame
already constructed in `RightModuleNakayama`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

/-- A chosen finite dual frame on a finitely generated projective right
module. -/
def projectiveFrame (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    FiniteProjectiveFrame Bᵐᵒᵖ P := by
  letI : Module.Projective Bᵐᵒᵖ P :=
    moduleProjective_of_fgProjective P (inferInstance : Projective P)
  exact finiteProjectiveFrame Bᵐᵒᵖ P

/-- The regular-Hom functional associated with one member of a projective
frame. -/
def projectiveFrameRegularHom (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (i : Fin (projectiveFrame P).n) : regularHomDualCarrier P :=
  rightRegularLinearEquiv.toLinearMap.comp ((projectiveFrame P).phi i)

/-- The rank-one right-module map determined by a regular-Hom functional
and an element of the target. -/
def projectiveRankOne (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (q : regularHomDualCarrier P) (y : Y) : P →ₗ[Bᵐᵒᵖ] Y where
  toFun p := MulOpposite.op (q p) • y
  map_add' p p' := by simp [add_smul]
  map_smul' r p := by
    change MulOpposite.op (q (r • p)) • y = r • MulOpposite.op (q p) • y
    rw [q.map_smul]
    simp [smul_smul]

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveRankOne_add_left (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (q q' : regularHomDualCarrier P) (y : Y) :
    projectiveRankOne P Y (q + q') y =
      projectiveRankOne P Y q y + projectiveRankOne P Y q' y := by
  ext p
  simp [projectiveRankOne, add_smul]

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveRankOne_add_right (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (q : regularHomDualCarrier P) (y y' : Y) :
    projectiveRankOne P Y q (y + y') =
      projectiveRankOne P Y q y + projectiveRankOne P Y q y' := by
  ext p
  simp [projectiveRankOne, smul_add]

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveRankOne_balance (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (b : B) (q : regularHomDualCarrier P) (y : Y) :
    projectiveRankOne P Y q (MulOpposite.op b • y) =
      projectiveRankOne P Y (b • q) y := by
  ext p
  simp [projectiveRankOne, smul_smul]

omit [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveRankOne_smul_left (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (a : k) (q : regularHomDualCarrier P) (y : Y) :
    projectiveRankOne P Y (a • q) y =
      a • projectiveRankOne P Y q y := by
  rw [← IsScalarTower.algebraMap_smul B a q]
  rw [← projectiveRankOne_balance]
  rw [show MulOpposite.op (algebraMap k B a) =
    algebraMap k Bᵐᵒᵖ a by rfl]
  rw [IsScalarTower.algebraMap_smul Bᵐᵒᵖ a y]
  ext p
  change MulOpposite.op (q p) • a • y =
    a • MulOpposite.op (q p) • y
  exact smul_comm _ _ _

omit [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveRankOne_smul_right (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (a : k) (q : regularHomDualCarrier P) (y : Y) :
    projectiveRankOne P Y q (a • y) =
      a • projectiveRankOne P Y q y := by
  ext p
  change MulOpposite.op (q p) • a • y =
    a • MulOpposite.op (q p) • y
  exact smul_comm _ _ _

/-- Evaluation of a dual Hom functional against the rank-one pairing. -/
def nakayamaHomValue (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (ell : Module.Dual k (P →ₗ[Bᵐᵒᵖ] Y)) (y : Y) :
    projectiveNakayamaFGObj (k := k) P := by
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  change Module.Dual k Q
  exact
    { toFun := fun q ↦ ell (projectiveRankOne P Y q y)
      map_add' := fun q q' ↦ by
        rw [projectiveRankOne_add_left, map_add]
      map_smul' := fun a q ↦ by
        change ell (projectiveRankOne P Y ((algebraMap k B a) • q) y) =
          a * ell (projectiveRankOne P Y q y)
        rw [← projectiveRankOne_balance]
        rw [show MulOpposite.op (algebraMap k B a) =
          algebraMap k Bᵐᵒᵖ a by rfl]
        rw [IsScalarTower.algebraMap_smul Bᵐᵒᵖ a y]
        rw [projectiveRankOne_smul_right, map_smul]
        rfl }

/-- The Nakayama--Hom pairing as a right-module map in the variable
module. -/
def nakayamaHomRLinear (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (ell : Module.Dual k (P →ₗ[Bᵐᵒᵖ] Y)) :
    Y →ₗ[Bᵐᵒᵖ] projectiveNakayamaFGObj (k := k) P where
  toFun := nakayamaHomValue (k := k) P Y ell
  map_add' y y' := by
    let Q := regularHomDualFGObj (k := k) P
    letI : Module k Q := Module.restrictScalars k B Q
    apply (Contragredient.forwardInnerDualEquiv k B Q).injective
    apply LinearMap.ext
    intro q
    change ell (projectiveRankOne P Y q (y + y')) =
      ell (projectiveRankOne P Y q y) + ell (projectiveRankOne P Y q y')
    rw [projectiveRankOne_add_right, map_add]
  map_smul' b y := by
    let Q := regularHomDualFGObj (k := k) P
    letI : Module k Q := Module.restrictScalars k B Q
    apply (Contragredient.forwardInnerDualEquiv k B Q).injective
    apply LinearMap.ext
    intro q
    change ell (projectiveRankOne P Y q (b • y)) =
      ell (projectiveRankOne P Y (b.unop • q) y)
    change ell (projectiveRankOne P Y q (MulOpposite.op b.unop • y)) = _
    rw [projectiveRankOne_balance]

/-- The Nakayama--Hom pairing as a `k`-linear map. -/
def nakayamaHomLinearMap (P Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    Module.Dual k (P →ₗ[Bᵐᵒᵖ] Y) →ₗ[k]
      (Y →ₗ[Bᵐᵒᵖ] projectiveNakayamaFGObj (k := k) P) where
  toFun := nakayamaHomRLinear (k := k) P Y
  map_add' ell mu := by
    apply LinearMap.ext
    intro y
    let Q := regularHomDualFGObj (k := k) P
    letI : Module k Q := Module.restrictScalars k B Q
    apply (Contragredient.forwardInnerDualEquiv k B Q).injective
    apply LinearMap.ext
    intro q
    change (ell + mu) (projectiveRankOne P Y q y) =
      ell (projectiveRankOne P Y q y) + mu (projectiveRankOne P Y q y)
    rw [LinearMap.add_apply]
  map_smul' a ell := by
    apply LinearMap.ext
    intro y
    let Q := regularHomDualFGObj (k := k) P
    letI : Module k Q := Module.restrictScalars k B Q
    apply (Contragredient.forwardInnerDualEquiv k B Q).injective
    apply LinearMap.ext
    intro q
    change a * ell (projectiveRankOne P Y q y) =
      ell (projectiveRankOne P Y ((algebraMap k B a) • q) y)
    rw [← projectiveRankOne_balance]
    rw [show MulOpposite.op (algebraMap k B a) =
      algebraMap k Bᵐᵒᵖ a by rfl]
    rw [IsScalarTower.algebraMap_smul Bᵐᵒᵖ a y]
    rw [projectiveRankOne_smul_right, map_smul]
    rfl

/-- The chosen projective frame expands every morphism as a finite sum of
rank-one maps. -/
theorem projectiveRankOne_frame_sum
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (f : P →ₗ[Bᵐᵒᵖ] Y) :
    ∑ i, projectiveRankOne P Y (projectiveFrameRegularHom P i)
        (f ((projectiveFrame P).p i)) = f := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.sum_apply]
  change (∑ i, (projectiveFrame P).phi i p •
      f ((projectiveFrame P).p i)) = f p
  calc
    _ = f (∑ i, (projectiveFrame P).phi i p •
        (projectiveFrame P).p i) := by simp
    _ = f p := by rw [(projectiveFrame P).total]

/-- The same frame reconstructs every element of the regular Hom-dual. -/
theorem regularHomDual_frame_sum
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (q : regularHomDualCarrier P) :
    ∑ i, q ((projectiveFrame P).p i) •
        projectiveFrameRegularHom P i = q := by
  apply LinearMap.ext
  intro p
  have h := congrArg q ((projectiveFrame P).total p)
  simpa [projectiveFrameRegularHom, rightRegularLinearEquiv,
    map_sum] using h

/-- Recover a map of finite projective right modules from the induced map
between their regular Hom-duals. -/
def regularHomDualMapPreimage
    (P Q : FGModuleCat.{u} Bᵐᵒᵖ) [Projective Q]
    (h : regularHomDualFGObj (k := k) Q ⟶
      regularHomDualFGObj (k := k) P) : P ⟶ Q :=
  FGModuleCat.ofHom
    { toFun := fun p ↦ ∑ i,
        MulOpposite.op
          ((h.hom.hom (projectiveFrameRegularHom Q i)) p) •
            (projectiveFrame Q).p i
      map_add' := by
        intro p p'
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_add]
        simp only [MulOpposite.op_add, add_smul]
      map_smul' := by
        intro r p
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        change MulOpposite.op
            ((h.hom.hom (projectiveFrameRegularHom Q i)) (r • p)) •
              (projectiveFrame Q).p i =
          r • (MulOpposite.op
            ((h.hom.hom (projectiveFrameRegularHom Q i)) p) •
              (projectiveFrame Q).p i)
        rw [(h.hom.hom (projectiveFrameRegularHom Q i)).map_smul]
        simp [smul_smul] }

/-- Regular-Hom dualization is full on finite projective right modules. -/
theorem regularHomDualMap_preimage
    (P Q : FGModuleCat.{u} Bᵐᵒᵖ) [Projective Q]
    (h : regularHomDualFGObj (k := k) Q ⟶
      regularHomDualFGObj (k := k) P) :
    regularHomDualMap (k := k) (regularHomDualMapPreimage (k := k) P Q h) = h := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro p
  change q ((regularHomDualMapPreimage (k := k) P Q h).hom.hom p) =
    h.hom.hom q p
  change q (∑ i, MulOpposite.op
      ((h.hom.hom (projectiveFrameRegularHom Q i)) p) •
        (projectiveFrame Q).p i) =
    h.hom.hom q p
  calc
    _ = (∑ i, q ((projectiveFrame Q).p i) •
        h.hom.hom (projectiveFrameRegularHom Q i)) p := by
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, LinearMap.smul_apply]
      rfl
    _ = h.hom.hom (∑ i, q ((projectiveFrame Q).p i) •
        projectiveFrameRegularHom Q i) p := by
      rw [map_sum]
      simp only [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, LinearMap.smul_apply]
    _ = h.hom.hom q p := by
      rw [regularHomDual_frame_sum]

/-- Recover a map of finite projective right modules from a morphism between
their Nakayama objects. -/
def projectiveNakayamaMapPreimage
    (P Q : FGModuleCat.{u} Bᵐᵒᵖ) [Projective Q]
    (a : projectiveNakayamaFGObj (k := k) P ⟶
      projectiveNakayamaFGObj (k := k) Q) : P ⟶ Q := by
  letI : (Contragredient.dualFunctor k B).Full :=
    (Contragredient.dualityEquivalence k B).fullyFaithfulFunctor.full
  letI : (Contragredient.dualFunctor k B).Faithful :=
    (Contragredient.dualityEquivalence k B).fullyFaithfulFunctor.faithful
  exact regularHomDualMapPreimage (k := k) P Q
    ((Contragredient.dualFunctor k B).preimage a).unop

/-- The concrete Nakayama construction is full on finite projectives. -/
theorem projectiveNakayamaMap_preimage
    (P Q : FGModuleCat.{u} Bᵐᵒᵖ) [Projective Q]
    (a : projectiveNakayamaFGObj (k := k) P ⟶
      projectiveNakayamaFGObj (k := k) Q) :
    projectiveNakayamaMap (k := k)
      (projectiveNakayamaMapPreimage (k := k) P Q a) = a := by
  letI : (Contragredient.dualFunctor k B).Full :=
    (Contragredient.dualityEquivalence k B).fullyFaithfulFunctor.full
  letI : (Contragredient.dualFunctor k B).Faithful :=
    (Contragredient.dualityEquivalence k B).fullyFaithfulFunctor.faithful
  calc
    _ = (Contragredient.dualFunctor k B).map
        ((Contragredient.dualFunctor k B).preimage a) := by
      change (Contragredient.dualFunctor k B).map
          (regularHomDualMap (k := k)
            (projectiveNakayamaMapPreimage (k := k) P Q a)).op =
        (Contragredient.dualFunctor k B).map
          ((Contragredient.dualFunctor k B).preimage a)
      rw [(Contragredient.dualFunctor k B).map_injective_iff]
      change
        (regularHomDualMap (k := k)
          (projectiveNakayamaMapPreimage (k := k) P Q a)).op =
          (Contragredient.dualFunctor k B).preimage a
      apply Quiver.Hom.unop_inj
      rw [Quiver.Hom.unop_op]
      dsimp only [projectiveNakayamaMapPreimage]
      rw [regularHomDualMap_preimage]
    _ = a := (Contragredient.dualFunctor k B).map_preimage a

/-- The concrete Nakayama construction is faithful on finite projectives. -/
theorem projectiveNakayamaMap_injective
    (P Q : FGModuleCat.{u} Bᵐᵒᵖ) [Projective Q] :
    Function.Injective (fun d : P ⟶ Q ↦
      projectiveNakayamaMap (k := k) d) := by
  intro d e hde
  change projectiveNakayamaMap (k := k) d =
    projectiveNakayamaMap (k := k) e at hde
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  apply nakayamaUnitElement_injective (k := k) Q inferInstance
  rw [← nakayamaUnitElement_naturality,
    ← nakayamaUnitElement_naturality, hde]

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaMap_comp
    {P Q T : FGModuleCat.{u} Bᵐᵒᵖ} (d : P ⟶ Q) (e : Q ⟶ T) :
    projectiveNakayamaMap (k := k) (d ≫ e) =
      projectiveNakayamaMap (k := k) d ≫
        projectiveNakayamaMap (k := k) e := by
  apply FGModuleCat.hom_ext
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaMap_id
    (P : FGModuleCat.{u} Bᵐᵒᵖ) :
    projectiveNakayamaMap (k := k) (𝟙 P) = 𝟙 _ := by
  apply FGModuleCat.hom_ext
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaMap_add
    {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (d e : P ⟶ Q) :
    projectiveNakayamaMap (k := k) (d + e) =
      projectiveNakayamaMap (k := k) d +
        projectiveNakayamaMap (k := k) e := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  apply (Contragredient.forwardInnerDualEquiv k B
    (regularHomDualFGObj (k := k) Q)).injective
  apply DFunLike.ext _ _
  intro q
  change (Contragredient.forwardInnerDualEquiv k B
      (regularHomDualFGObj (k := k) P) ell)
      ((regularHomDualMap (k := k) (d + e)).hom.hom q) =
    (Contragredient.forwardInnerDualEquiv k B
      (regularHomDualFGObj (k := k) P) ell)
        ((regularHomDualMap (k := k) d).hom.hom q) +
      (Contragredient.forwardInnerDualEquiv k B
        (regularHomDualFGObj (k := k) P) ell)
        ((regularHomDualMap (k := k) e).hom.hom q)
  rw [show (regularHomDualMap (k := k) (d + e)).hom.hom q =
      (regularHomDualMap (k := k) d).hom.hom q +
        (regularHomDualMap (k := k) e).hom.hom q by
    apply LinearMap.ext
    intro p
    change q (d.hom.hom p + e.hom.hom p) =
      q (d.hom.hom p) + q (e.hom.hom p)
    exact map_add q _ _]
  exact map_add _ _ _

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaMap_smul
    {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (c : k) (d : P ⟶ Q) :
    projectiveNakayamaMap (k := k) (c • d) =
      c • projectiveNakayamaMap (k := k) d := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  apply (Contragredient.forwardInnerDualEquiv k B
    (regularHomDualFGObj (k := k) Q)).injective
  apply DFunLike.ext _ _
  intro q
  rw [show (c • projectiveNakayamaMap (k := k) d).hom.hom ell =
      c • (projectiveNakayamaMap (k := k) d).hom.hom ell by rfl]
  rw [map_smul]
  change (Contragredient.forwardInnerDualEquiv k B
      (regularHomDualFGObj (k := k) P) ell)
      ((regularHomDualMap (k := k) (c • d)).hom.hom q) =
    c • (Contragredient.forwardInnerDualEquiv k B
      (regularHomDualFGObj (k := k) P) ell)
      ((regularHomDualMap (k := k) d).hom.hom q)
  rw [show (regularHomDualMap (k := k) (c • d)).hom.hom q =
      c • (regularHomDualMap (k := k) d).hom.hom q by
    apply LinearMap.ext
    intro p
    change q (c • d.hom.hom p) = c • q (d.hom.hom p)
    exact q.map_smul_of_tower c _]
  let phi := Contragredient.forwardInnerDualEquiv k B
    (regularHomDualFGObj (k := k) P) ell
  let v := (regularHomDualMap (k := k) d).hom.hom q
  let oldSmul := c • v
  change phi oldSmul = c * phi v
  let newSmul := @SMul.smul k _
    (Contragredient.moduleKOfFGModule k B
      (regularHomDualFGObj (k := k) P)).toDistribSMul.toSMul c v
  have hold : oldSmul = newSmul := by
    have hnew : newSmul = (algebraMap k B c) • v := rfl
    rw [hnew]
    apply LinearMap.ext
    intro p
    simp [oldSmul, Algebra.smul_def]
  have hphi := @LinearMap.map_smul k _ _ inferInstance inferInstance
    inferInstance
    (Contragredient.moduleKOfFGModule k B
      (regularHomDualFGObj (k := k) P))
    inferInstance phi c v
  change phi newSmul = c * phi v at hphi
  exact (congrArg phi hold).trans hphi

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaMap_sub
    {P Q : FGModuleCat.{u} Bᵐᵒᵖ} (d e : P ⟶ Q) :
    projectiveNakayamaMap (k := k) (d - e) =
      projectiveNakayamaMap (k := k) d -
        projectiveNakayamaMap (k := k) e := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  apply (Contragredient.forwardInnerDualEquiv k B
    (regularHomDualFGObj (k := k) Q)).injective
  apply DFunLike.ext _ _
  intro q
  change (Contragredient.forwardInnerDualEquiv k B
      (regularHomDualFGObj (k := k) P) ell)
      ((regularHomDualMap (k := k) (d - e)).hom.hom q) =
    (Contragredient.forwardInnerDualEquiv k B
      (regularHomDualFGObj (k := k) P) ell)
        ((regularHomDualMap (k := k) d).hom.hom q) -
      (Contragredient.forwardInnerDualEquiv k B
        (regularHomDualFGObj (k := k) P) ell)
        ((regularHomDualMap (k := k) e).hom.hom q)
  rw [show (regularHomDualMap (k := k) (d - e)).hom.hom q =
      (regularHomDualMap (k := k) d).hom.hom q -
        (regularHomDualMap (k := k) e).hom.hom q by
    apply LinearMap.ext
    intro p
    change q (d.hom.hom p - e.hom.hom p) =
      q (d.hom.hom p) - q (e.hom.hom p)
    exact map_sub q _ _]
  exact map_sub _ _ _

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaMap_zero
    (P Q : FGModuleCat.{u} Bᵐᵒᵖ) :
    projectiveNakayamaMap (k := k) (0 : P ⟶ Q) = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  apply (Contragredient.forwardInnerDualEquiv k B
    (regularHomDualFGObj (k := k) Q)).injective
  apply DFunLike.ext _ _
  intro q
  change (Contragredient.forwardInnerDualEquiv k B
      (regularHomDualFGObj (k := k) P) ell)
        ((regularHomDualMap (k := k) (0 : P ⟶ Q)).hom.hom q) = 0
  have hqzero :
      (regularHomDualMap (k := k) (0 : P ⟶ Q)).hom.hom q = 0 := by
    apply LinearMap.ext
    intro p
    change q ((0 : P →ₗ[Bᵐᵒᵖ] Q) p) = 0
    rw [LinearMap.zero_apply, map_zero]
  rw [hqzero, map_zero]

/-- On a finite projective right module, the concrete Nakayama functor
induces an equivalence of endomorphism rings. -/
noncomputable def projectiveNakayamaEndRingEquiv
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    End P ≃+* End (projectiveNakayamaFGObj (k := k) P) :=
  { toFun := fun f ↦ End.of
      (projectiveNakayamaMap (k := k) (End.asHom f))
    invFun := fun f ↦ End.of
      (projectiveNakayamaMapPreimage (k := k) P P (End.asHom f))
    left_inv := by
      intro f
      apply End.ext
      apply projectiveNakayamaMap_injective (k := k) P P
      change projectiveNakayamaMap (k := k)
          (projectiveNakayamaMapPreimage (k := k) P P
            (projectiveNakayamaMap (k := k) (End.asHom f))) =
        projectiveNakayamaMap (k := k) (End.asHom f)
      rw [projectiveNakayamaMap_preimage]
    right_inv := by
      intro f
      apply End.ext
      exact projectiveNakayamaMap_preimage
        (k := k) P P (End.asHom f)
    map_add' := by
      intro f g
      apply End.ext
      exact projectiveNakayamaMap_add
        (k := k) (End.asHom f) (End.asHom g)
    map_mul' := by
      intro f g
      apply End.ext
      simpa only [End.mul_def] using
        (projectiveNakayamaMap_comp
          (k := k) (End.asHom g) (End.asHom f)) }

/-- Coordinates of the regular Hom-dual in the frame inherited from `P`. -/
def regularHomDualFreeSection
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    regularHomDualCarrier P →ₗ[B] (Fin (projectiveFrame P).n → B) where
  toFun := fun q i ↦ q ((projectiveFrame P).p i)
  map_add' := by intros; ext i; simp
  map_smul' := by intros; ext i; rfl

/-- Reconstruction from the inherited regular-Hom frame. -/
def regularHomDualFreeRetraction
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    (Fin (projectiveFrame P).n → B) →ₗ[B] regularHomDualCarrier P where
  toFun := fun v ↦ ∑ i, v i • projectiveFrameRegularHom P i
  map_add' v w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [add_smul]
  map_smul' b v := by
    apply LinearMap.ext
    intro p
    simp [Finset.mul_sum, mul_assoc]

/-- The regular Hom-dual of a finite projective right module is a finite
projective left module. -/
theorem regularHomDual_moduleProjective
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    Module.Projective B (regularHomDualCarrier P) := by
  apply Module.Projective.of_split
    (regularHomDualFreeSection P) (regularHomDualFreeRetraction P)
  apply LinearMap.ext
  intro q
  exact regularHomDual_frame_sum P q

/-- The concrete Nakayama object of a finite projective right module is
injective. -/
theorem projectiveNakayamaFGObj_injective
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    Injective (projectiveNakayamaFGObj (k := k) P) := by
  have hP : Projective (regularHomDualFGObj (k := k) P) := by
    apply fgProjective_of_moduleProjective
    exact regularHomDual_moduleProjective P
  have hop : Injective
      (Opposite.op (regularHomDualFGObj (k := k) P)) :=
    Injective.projective_iff_injective_op.mp hP
  exact ((Contragredient.dualityEquivalence k B).map_injective_iff
    (Opposite.op (regularHomDualFGObj (k := k) P))).2 hop

/-- The Nakayama--Hom pairing is injective for a projective source. -/
theorem nakayamaHomLinearMap_injective
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    Function.Injective (nakayamaHomLinearMap (k := k) P Y) := by
  intro ell mu h
  apply LinearMap.ext
  intro f
  have hf := projectiveRankOne_frame_sum P Y f
  rw [← hf, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hy := LinearMap.congr_fun h (f ((projectiveFrame P).p i))
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  have hq := congrArg
    (fun z : projectiveNakayamaFGObj (k := k) P ↦
      (Contragredient.forwardInnerDualEquiv k B Q z)
        (projectiveFrameRegularHom P i)) hy
  exact hq

/-- Evaluation of an element of `nu P` on the regular-Hom dual. -/
def projectiveNakayamaEvaluation (P : FGModuleCat.{u} Bᵐᵒᵖ)
    (z : projectiveNakayamaFGObj (k := k) P)
    (q : regularHomDualFGObj (k := k) P) : k := by
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  exact (Contragredient.forwardInnerDualEquiv k B Q z) q

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaEvaluation_add
    (P : FGModuleCat.{u} Bᵐᵒᵖ)
    (z z' : projectiveNakayamaFGObj (k := k) P)
    (q : regularHomDualFGObj (k := k) P) :
    projectiveNakayamaEvaluation (k := k) P (z + z') q =
      projectiveNakayamaEvaluation (k := k) P z q +
        projectiveNakayamaEvaluation (k := k) P z' q := by
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  change
    (Contragredient.forwardInnerDualEquiv k B Q (z + z')) q =
      (Contragredient.forwardInnerDualEquiv k B Q z) q +
        (Contragredient.forwardInnerDualEquiv k B Q z') q
  rw [map_add]
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaEvaluation_smul
    (P : FGModuleCat.{u} Bᵐᵒᵖ)
    (b : Bᵐᵒᵖ) (z : projectiveNakayamaFGObj (k := k) P)
    (q : regularHomDualFGObj (k := k) P) :
    projectiveNakayamaEvaluation (k := k) P (b • z) q =
      projectiveNakayamaEvaluation (k := k) P z (b.unop • q) := by
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaEvaluation_ksmul
    (P : FGModuleCat.{u} Bᵐᵒᵖ)
    (a : k) (z : projectiveNakayamaFGObj (k := k) P)
    (q : regularHomDualFGObj (k := k) P) :
    projectiveNakayamaEvaluation (k := k) P (a • z) q =
      a * projectiveNakayamaEvaluation (k := k) P z q := by
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  exact congrArg (fun ell ↦ ell q)
    ((Contragredient.forwardInnerDualEquiv k B Q).map_smul a z)

omit [IsNoetherianRing Bᵐᵒᵖ] in
theorem projectiveNakayamaEvaluation_sum
    (P : FGModuleCat.{u} Bᵐᵒᵖ)
    {n : ℕ} (z : projectiveNakayamaFGObj (k := k) P)
    (v : Fin n → regularHomDualFGObj (k := k) P) :
    projectiveNakayamaEvaluation (k := k) P z (∑ i, v i) =
      ∑ i, projectiveNakayamaEvaluation (k := k) P z (v i) := by
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  change
    (Contragredient.forwardInnerDualEquiv k B Q z) (∑ i, v i) =
      ∑ i, (Contragredient.forwardInnerDualEquiv k B Q z) (v i)
  rw [map_sum]

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem projectiveNakayamaEvaluation_nakayamaHomValue
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (ell : Module.Dual k (P →ₗ[Bᵐᵒᵖ] Y)) (y : Y)
    (q : regularHomDualFGObj (k := k) P) :
    projectiveNakayamaEvaluation (k := k) P
        (nakayamaHomValue (k := k) P Y ell y) q =
      ell (projectiveRankOne P Y q y) := by
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  rfl

/-- The explicit inverse functional furnished by the projective frame. -/
def nakayamaHomInverseFunctional
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (g : Y →ₗ[Bᵐᵒᵖ] projectiveNakayamaFGObj (k := k) P) :
    Module.Dual k (P →ₗ[Bᵐᵒᵖ] Y) where
  toFun := fun f ↦ ∑ i,
    projectiveNakayamaEvaluation (k := k) P
      (g (f ((projectiveFrame P).p i)))
      (projectiveFrameRegularHom P i)
  map_add' f f' := by
    simp [Finset.sum_add_distrib]
  map_smul' a f := by
    change (∑ i,
      projectiveNakayamaEvaluation (k := k) P
        (g ((a • f) ((projectiveFrame P).p i)))
        (projectiveFrameRegularHom P i)) =
      a * ∑ i,
        projectiveNakayamaEvaluation (k := k) P
          (g (f ((projectiveFrame P).p i)))
          (projectiveFrameRegularHom P i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hg := (g.restrictScalars k).map_smul a
      (f ((projectiveFrame P).p i))
    change g (a • f ((projectiveFrame P).p i)) =
      a • g (f ((projectiveFrame P).p i)) at hg
    rw [LinearMap.smul_apply, hg, projectiveNakayamaEvaluation_ksmul]

/-- The Nakayama--Hom pairing is surjective for a projective source. -/
theorem nakayamaHomLinearMap_surjective
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    Function.Surjective (nakayamaHomLinearMap (k := k) P Y) := by
  intro g
  refine ⟨nakayamaHomInverseFunctional (k := k) P Y g, ?_⟩
  apply LinearMap.ext
  intro y
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  apply (Contragredient.forwardInnerDualEquiv k B Q).injective
  apply LinearMap.ext
  intro q
  change
    (∑ i, projectiveNakayamaEvaluation (k := k) P
      (g (projectiveRankOne P Y q y ((projectiveFrame P).p i)))
      (projectiveFrameRegularHom P i)) =
      projectiveNakayamaEvaluation (k := k) P (g y) q
  calc
    _ = ∑ i, projectiveNakayamaEvaluation (k := k) P (g y)
        (q ((projectiveFrame P).p i) •
          projectiveFrameRegularHom P i) := by
      apply Finset.sum_congr rfl
      intro i _
      change projectiveNakayamaEvaluation (k := k) P
          (g (MulOpposite.op (q ((projectiveFrame P).p i)) • y))
          (projectiveFrameRegularHom P i) = _
      rw [g.map_smul, projectiveNakayamaEvaluation_smul]
      simp
    _ = projectiveNakayamaEvaluation (k := k) P (g y)
        (∑ i, q ((projectiveFrame P).p i) •
          projectiveFrameRegularHom P i) := by
      rw [projectiveNakayamaEvaluation_sum]
    _ = projectiveNakayamaEvaluation (k := k) P (g y) q := by
      rw [regularHomDual_frame_sum]

/-- The concrete finite-projective Nakayama--Hom comparison. -/
def nakayamaHomLinearEquiv
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    Module.Dual k (P →ₗ[Bᵐᵒᵖ] Y) ≃ₗ[k]
      (Y →ₗ[Bᵐᵒᵖ] projectiveNakayamaFGObj (k := k) P) :=
  LinearEquiv.ofBijective (nakayamaHomLinearMap (k := k) P Y)
    ⟨nakayamaHomLinearMap_injective (k := k) P Y,
      nakayamaHomLinearMap_surjective (k := k) P Y⟩

/-- Categorical morphisms in `FGModuleCat` identified with their underlying
right-module maps, including the restricted `k`-linear structure. -/
def fgHomCarrierLinearEquiv (Y Z : FGModuleCat.{u} Bᵐᵒᵖ) :
    (Y ⟶ Z) ≃ₗ[k] (Y →ₗ[Bᵐᵒᵖ] Z) :=
  InducedCategory.homLinearEquiv.trans ModuleCat.homLinearEquiv

/-- The field-valued Nakayama--Hom equivalence in categorical form. -/
def fieldNakayamaHomEquiv
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    (Y ⟶ projectiveNakayamaFGObj (k := k) P) ≃ₗ[k]
      ((P ⟶ Y) →ₗ[k] k) :=
  (fgHomCarrierLinearEquiv (k := k) Y
      (projectiveNakayamaFGObj (k := k) P)).trans <|
    (nakayamaHomLinearEquiv (k := k) P Y).symm |>.trans <|
      (LinearEquiv.congrLeft k k
        (fgHomCarrierLinearEquiv (k := k) P Y)).symm

@[simp]
theorem fieldNakayamaHomEquiv_rankOne
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (a : Y ⟶ projectiveNakayamaFGObj (k := k) P)
    (q : regularHomDualFGObj (k := k) P) (y : Y) :
    fieldNakayamaHomEquiv (k := k) P Y a
        (FGModuleCat.ofHom (projectiveRankOne P Y q y)) =
      projectiveNakayamaEvaluation (k := k) P (a.hom.hom y) q := by
  let e := nakayamaHomLinearEquiv (k := k) P Y
  let ell := e.symm a.hom.hom
  have h := e.apply_symm_apply a.hom.hom
  have hy := LinearMap.congr_fun h y
  let Q := regularHomDualFGObj (k := k) P
  letI : Module k Q := Module.restrictScalars k B Q
  have hq := congrArg
    (fun z : projectiveNakayamaFGObj (k := k) P ↦
      (Contragredient.forwardInnerDualEquiv k B Q z) q) hy
  exact hq

include k in
omit [FiniteDimensional k B] in
/-- The categorical finite rank-one expansion. -/
theorem categoricalProjectiveRankOne_frame_sum
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (f : P ⟶ Y) :
    ∑ i, FGModuleCat.ofHom
        (projectiveRankOne P Y (projectiveFrameRegularHom P i)
          (f.hom.hom ((projectiveFrame P).p i))) = f := by
  apply (fgHomCarrierLinearEquiv (k := k) P Y).injective
  rw [map_sum]
  change ∑ i, projectiveRankOne P Y (projectiveFrameRegularHom P i)
      (f.hom.hom ((projectiveFrame P).p i)) = f.hom.hom
  exact projectiveRankOne_frame_sum P Y f.hom.hom

/-- Every value of the categorical comparison is its finite-frame sum. -/
theorem fieldNakayamaHomEquiv_apply_eq_sum
    (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (a : Y ⟶ projectiveNakayamaFGObj (k := k) P)
    (f : P ⟶ Y) :
    fieldNakayamaHomEquiv (k := k) P Y a f =
      ∑ i, projectiveNakayamaEvaluation (k := k) P
        (a.hom.hom (f.hom.hom ((projectiveFrame P).p i)))
        (projectiveFrameRegularHom P i) := by
  let s := ∑ i, FGModuleCat.ofHom
    (projectiveRankOne P Y (projectiveFrameRegularHom P i)
      (f.hom.hom ((projectiveFrame P).p i)))
  have hs : s = f := categoricalProjectiveRankOne_frame_sum (k := k) P Y f
  calc
    _ = fieldNakayamaHomEquiv (k := k) P Y a s := by rw [hs]
    _ = ∑ i, fieldNakayamaHomEquiv (k := k) P Y a
        (FGModuleCat.ofHom
          (projectiveRankOne P Y (projectiveFrameRegularHom P i)
            (f.hom.hom ((projectiveFrame P).p i)))) := by rw [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fieldNakayamaHomEquiv_rankOne]

/-- Naturality of the field Nakayama--Hom comparison in the variable
module. -/
theorem fieldNakayamaHomEquiv_naturality
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    {Y Z : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ Z)
    (a : Z ⟶ projectiveNakayamaFGObj (k := k) P)
    (f : P ⟶ Y) :
    fieldNakayamaHomEquiv (k := k) P Y (g ≫ a) f =
      fieldNakayamaHomEquiv (k := k) P Z a (f ≫ g) := by
  rw [fieldNakayamaHomEquiv_apply_eq_sum,
    fieldNakayamaHomEquiv_apply_eq_sum]
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
/-- Rank-one maps are natural in their projective source. -/
theorem projectiveRankOne_projectiveNaturality
    {P' P : FGModuleCat.{u} Bᵐᵒᵖ} (d : P' ⟶ P)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (q : regularHomDualCarrier P) (y : Y) :
    (projectiveRankOne P Y q y).comp d.hom.hom =
      projectiveRankOne P' Y
        ((regularHomDualMap (k := k) d).hom.hom q) y := by
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
/-- Evaluation is natural under the covariant Nakayama map. -/
theorem projectiveNakayamaEvaluation_map
    {P' P : FGModuleCat.{u} Bᵐᵒᵖ} (d : P' ⟶ P)
    (z : projectiveNakayamaFGObj (k := k) P')
    (q : regularHomDualFGObj (k := k) P) :
    projectiveNakayamaEvaluation (k := k) P
        ((projectiveNakayamaMap (k := k) d).hom.hom z) q =
      projectiveNakayamaEvaluation (k := k) P' z
        ((regularHomDualMap (k := k) d).hom.hom q) := by
  let Q := regularHomDualFGObj (k := k) P
  let Q' := regularHomDualFGObj (k := k) P'
  letI : Module k Q := Module.restrictScalars k B Q
  letI : Module k Q' := Module.restrictScalars k B Q'
  rfl

include k in
/-- A projective-frame expansion remains valid after precomposition by a
map of projectives. -/
theorem categoricalProjectiveRankOne_projective_frame_sum
    {P' P : FGModuleCat.{u} Bᵐᵒᵖ} [Projective P]
    (d : P' ⟶ P) (Y : FGModuleCat.{u} Bᵐᵒᵖ) (f : P ⟶ Y) :
    ∑ i, FGModuleCat.ofHom
        (projectiveRankOne P' Y
          ((regularHomDualMap (k := k) d).hom.hom
            (projectiveFrameRegularHom P i))
          (f.hom.hom ((projectiveFrame P).p i))) = d ≫ f := by
  apply (fgHomCarrierLinearEquiv (k := k) P' Y).injective
  rw [map_sum]
  apply LinearMap.ext
  intro p'
  change
    (∑ i, projectiveRankOne P' Y
      ((regularHomDualMap (k := k) d).hom.hom
        (projectiveFrameRegularHom P i))
      (f.hom.hom ((projectiveFrame P).p i))) p' =
      f.hom.hom (d.hom.hom p')
  rw [LinearMap.sum_apply]
  calc
    _ = ∑ i, ((projectiveRankOne P Y
        (projectiveFrameRegularHom P i)
        (f.hom.hom ((projectiveFrame P).p i))).comp d.hom.hom) p' := by
      apply Finset.sum_congr rfl
      intro i _
      exact (LinearMap.congr_fun
        (projectiveRankOne_projectiveNaturality (k := k) d Y
          (projectiveFrameRegularHom P i)
          (f.hom.hom ((projectiveFrame P).p i))) p').symm
    _ = (∑ i, projectiveRankOne P Y
        (projectiveFrameRegularHom P i)
        (f.hom.hom ((projectiveFrame P).p i))) (d.hom.hom p') := by
      rw [LinearMap.sum_apply]
      simp only [LinearMap.comp_apply]
    _ = f.hom.hom (d.hom.hom p') := by
      rw [projectiveRankOne_frame_sum]

/-- Naturality of the Nakayama--Hom comparison in the finite-projective
variable. -/
theorem fieldNakayamaHomEquiv_projectiveNaturality
    {P' P : FGModuleCat.{u} Bᵐᵒᵖ} [Projective P'] [Projective P]
    (d : P' ⟶ P) (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (a : Y ⟶ projectiveNakayamaFGObj (k := k) P') (f : P ⟶ Y) :
    fieldNakayamaHomEquiv (k := k) P Y
        (a ≫ projectiveNakayamaMap (k := k) d) f =
      fieldNakayamaHomEquiv (k := k) P' Y a (d ≫ f) := by
  let s := ∑ i, FGModuleCat.ofHom
    (projectiveRankOne P' Y
      ((regularHomDualMap (k := k) d).hom.hom
        (projectiveFrameRegularHom P i))
      (f.hom.hom ((projectiveFrame P).p i)))
  have hs : s = d ≫ f :=
    categoricalProjectiveRankOne_projective_frame_sum
      (k := k) d Y f
  calc
    _ = ∑ i, projectiveNakayamaEvaluation (k := k) P
        ((a ≫ projectiveNakayamaMap (k := k) d).hom.hom
          (f.hom.hom ((projectiveFrame P).p i)))
        (projectiveFrameRegularHom P i) :=
      fieldNakayamaHomEquiv_apply_eq_sum (k := k) P Y _ f
    _ = ∑ i, projectiveNakayamaEvaluation (k := k) P'
        (a.hom.hom (f.hom.hom ((projectiveFrame P).p i)))
        ((regularHomDualMap (k := k) d).hom.hom
          (projectiveFrameRegularHom P i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact projectiveNakayamaEvaluation_map (k := k) d _ _
    _ = fieldNakayamaHomEquiv (k := k) P' Y a s := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [fieldNakayamaHomEquiv_rankOne]
    _ = fieldNakayamaHomEquiv (k := k) P' Y a (d ≫ f) := by
      rw [hs]

end MagnitudeConjecture.RightModule
