import MagnitudeConjecture.Algebra.RepresentationFiniteQuotient
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotient
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Modules over the primitive quotient

This file identifies finitely generated right modules over the manuscript's
literal primitive quotient `A/AeA` with the full subcategory of ambient right
`A`-modules annihilated by `AeA`.  The auxiliary quotient of `Aᵐᵒᵖ` is used
only to apply Mathlib's quotient-module API; an explicit algebra equivalence
returns every public categorical statement to `(A/AeA)ᵐᵒᵖ`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The opposite two-sided ideal used to construct right quotient modules
through Mathlib's left-module quotient API. -/
def primitiveLeftIdeal (e : A) : TwoSidedIdeal Aᵐᵒᵖ :=
  (primitiveIdeal e).op

/-- The auxiliary left-module quotient of `Aᵐᵒᵖ`. -/
abbrev PrimitiveLeftQuotient (e : A) :=
  Aᵐᵒᵖ ⧸ (primitiveLeftIdeal e).asIdeal

/-- The canonical algebra map `A ⟶ A/AeA`. -/
def primitiveQuotientAlgMap (e : A) :
    A →ₐ[k] primitiveQuotientAlgebra e :=
  (primitiveIdeal e).ringCon.mkₐ k

/-- The opposite quotient map, used to inflate right `A/AeA`-modules to
right `A`-modules. -/
def primitiveQuotientOpAlgMap (e : A) :
    Aᵐᵒᵖ →ₐ[k] (primitiveQuotientAlgebra e)ᵐᵒᵖ :=
  (primitiveQuotientAlgMap (k := k) e).op

omit [FiniteDimensional k A] in
theorem primitiveQuotientOpAlgMap_ker (e : A) :
    RingHom.ker (primitiveQuotientOpAlgMap (k := k) e) =
      (primitiveLeftIdeal e).asIdeal := by
  ext a
  rw [RingHom.mem_ker, TwoSidedIdeal.mem_asIdeal,
    primitiveLeftIdeal, TwoSidedIdeal.mem_op_iff]
  change MulOpposite.op (primitiveQuotientMap e a.unop) =
      MulOpposite.op 0 ↔ a.unop ∈ primitiveIdeal e
  rw [MulOpposite.op_inj]
  exact mem_primitiveIdeal_iff_quotient_eq_zero.symm

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem primitiveQuotientOpAlgMap_surjective (e : A) :
    Function.Surjective (primitiveQuotientOpAlgMap (k := k) e) := by
  intro b
  obtain ⟨a, ha⟩ := RingCon.mkₐ_surjective
    (α := k) (primitiveIdeal e).ringCon b.unop
  refine ⟨MulOpposite.op a, ?_⟩
  apply MulOpposite.unop_injective
  exact ha

/-- The auxiliary quotient of `Aᵐᵒᵖ` is canonically the opposite of the
manuscript's literal quotient `A/AeA`. -/
def primitiveLeftQuotientAlgEquiv (e : A) :
    PrimitiveLeftQuotient e ≃ₐ[k] (primitiveQuotientAlgebra e)ᵐᵒᵖ :=
  (Ideal.quotientEquivAlgOfEq k
      (primitiveQuotientOpAlgMap_ker (k := k) e).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (primitiveQuotientOpAlgMap_surjective (k := k) e))

noncomputable instance primitiveLeftQuotientModuleFinite (e : A) :
    Module.Finite k (PrimitiveLeftQuotient e) := by
  infer_instance

noncomputable instance primitiveQuotientOpModuleFinite (e : A) :
    Module.Finite k (primitiveQuotientAlgebra e)ᵐᵒᵖ :=
  Module.Finite.equiv (primitiveLeftQuotientAlgEquiv (k := k) e).toLinearEquiv

/-- The literal primitive quotient is finite-dimensional on the original
algebra side as well as on its opposite. -/
noncomputable instance primitiveQuotientModuleFinite (e : A) :
    Module.Finite k (primitiveQuotientAlgebra e) :=
  Module.Finite.equiv
    (MulOpposite.opLinearEquiv k :
      primitiveQuotientAlgebra e ≃ₗ[k]
        (primitiveQuotientAlgebra e)ᵐᵒᵖ).symm

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- An ambient right module annihilated by `AeA` is a module over the
auxiliary quotient of `Aᵐᵒᵖ`. -/
theorem isTorsionByPrimitiveLeftIdeal (e : A)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    Module.IsTorsionBySet Aᵐᵒᵖ M (primitiveLeftIdeal e).asIdeal := by
  intro m a
  exact hM m a.1.unop (by simpa [primitiveLeftIdeal] using a.2)

/-- The full subcategory of ambient right modules annihilated by `AeA`. -/
def PrimitiveQuotientProperty (e : A) :
    ObjectProperty (FinitelyGeneratedCategory A) :=
  fun M ↦ IsAnnihilatedBy (primitiveIdeal e) M

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- Annihilation by the primitive ideal is inherited by direct summands. -/
instance primitiveQuotientProperty_stableUnderRetracts (e : A) :
    (PrimitiveQuotientProperty e).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    change IsAnnihilatedBy (primitiveIdeal e) Y at hY
    change IsAnnihilatedBy (primitiveIdeal e) X
    intro x a ha
    have hzero := hY (r.i x) a ha
    apply_fun r.r at hzero
    have hri : r.r (r.i x) = x := by
      have h := congrArg (fun f : X ⟶ X ↦ f.hom.hom x) r.retract
      change r.r.hom.hom (r.i.hom.hom x) = x at h
      exact h
    simpa only [map_smul, map_zero, hri] using hzero

/-- The ambient realization of the finitely generated right
`A/AeA`-module category. -/
abbrev PrimitiveQuotientSubcategory (e : A) :=
  (PrimitiveQuotientProperty e).FullSubcategory

/-- An annihilated ambient module, regarded as a module over the auxiliary
left quotient. -/
def primitiveLeftObj (e : A) (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    ModuleCat (PrimitiveLeftQuotient e) := by
  let htor := isTorsionByPrimitiveLeftIdeal e M hM
  letI : Module (PrimitiveLeftQuotient e) M := htor.module
  exact ModuleCat.of (PrimitiveLeftQuotient e) M

/-- Passing to the auxiliary quotient does not change the underlying
finite-dimensional `k`-vector space. -/
def primitiveLeftObjLinearEquiv (e : A)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    M ≃ₗ[k] primitiveLeftObj e M hM := by
  let htor := isTorsionByPrimitiveLeftIdeal e M hM
  letI : Module (PrimitiveLeftQuotient e) M := htor.module
  change M ≃ₗ[k] ModuleCat.of (PrimitiveLeftQuotient e) M
  exact {
    toFun := fun m ↦ m
    invFun := fun m ↦ m
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := by
      intro c m
      change c • m =
        (Ideal.Quotient.mk (primitiveLeftIdeal e).asIdeal
          (algebraMap k Aᵐᵒᵖ c)) • m
      exact (htor.mk_smul (algebraMap k Aᵐᵒᵖ c) m).symm }

/-- Restriction from the auxiliary quotient recovers the original ambient
module by the identity on its carrier. -/
def primitiveLeftObjRestrictIso (e : A)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    (ModuleCat.restrictScalars
      (Ideal.Quotient.mk (primitiveLeftIdeal e).asIdeal)).obj
        (primitiveLeftObj e M hM) ≅ M.obj := by
  let htor := isTorsionByPrimitiveLeftIdeal e M hM
  letI : Module (PrimitiveLeftQuotient e) M := htor.module
  change (ModuleCat.restrictScalars
    (Ideal.Quotient.mk (primitiveLeftIdeal e).asIdeal)).obj
      (ModuleCat.of (PrimitiveLeftQuotient e) M) ≅ M.obj
  exact LinearEquiv.toModuleIso {
    toFun := fun m ↦ m
    invFun := fun m ↦ m
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun a m ↦ htor.mk_smul a m }

/-- Every ambient morphism between annihilated modules is linear over the
auxiliary quotient. -/
def primitiveLeftMap (e : A)
    (M N : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M)
    (hN : IsAnnihilatedBy (primitiveIdeal e) N)
    (f : M ⟶ N) :
    primitiveLeftObj e M hM ⟶ primitiveLeftObj e N hN := by
  let hMtor := isTorsionByPrimitiveLeftIdeal e M hM
  let hNtor := isTorsionByPrimitiveLeftIdeal e N hN
  letI : Module (PrimitiveLeftQuotient e) M := hMtor.module
  letI : Module (PrimitiveLeftQuotient e) N := hNtor.module
  exact ModuleCat.ofHom {
    toFun := f
    map_add' := f.hom.hom.map_add
    map_smul' := by
      intro b m
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp only [RingHom.id_apply]
      rw [hNtor.mk_smul]
      exact f.hom.hom.map_smul a m }

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem primitiveLeftMap_apply (e : A)
    (M N : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M)
    (hN : IsAnnihilatedBy (primitiveIdeal e) N)
    (f : M ⟶ N) (m : M) :
    primitiveLeftMap e M N hM hN f m = f m := rfl

/-- The auxiliary quotient object bundled in the finitely generated module
category. -/
def primitiveLeftFGObj (e : A) (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    FGModuleCat.{u} (PrimitiveLeftQuotient e) := by
  letI : Module.Finite k (primitiveLeftObj e M hM) := by
    letI : Module.Finite k M :=
      finite_over_field_of_finitelyGenerated k A M
    exact Module.Finite.equiv (primitiveLeftObjLinearEquiv e M hM)
  letI : Module.Finite (PrimitiveLeftQuotient e)
      (primitiveLeftObj e M hM) :=
    Module.Finite.of_restrictScalars_finite k (PrimitiveLeftQuotient e)
      (primitiveLeftObj e M hM)
  exact FGModuleCat.of (PrimitiveLeftQuotient e) (primitiveLeftObj e M hM)

/-- Passage from the annihilated ambient subcategory to modules over the
auxiliary quotient. -/
def primitiveLeftFunctor (e : A) :
    PrimitiveQuotientSubcategory e ⥤ FGModuleCat.{u} (PrimitiveLeftQuotient e) where
  obj M := primitiveLeftFGObj (k := k) e M.obj M.property
  map {M N} f := ObjectProperty.homMk
    (primitiveLeftMap e M.obj N.obj M.property N.property f.hom)
  map_id M := by
    apply FGModuleCat.hom_ext
    ext m
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    ext m
    rfl

/-- The quotient realization functor preserves the preadditive structure. -/
noncomputable instance primitiveLeftFunctorAdditive (e : A) :
    (primitiveLeftFunctor (k := k) e).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    rfl

/-- Passage to the auxiliary quotient is linear over the ground field. -/
noncomputable instance primitiveLeftFunctorLinear (e : A) :
    (primitiveLeftFunctor (k := k) e).Linear k where
  map_smul := by
    intro M N f a
    apply ObjectProperty.hom_ext
    rfl

/-- Inflate an auxiliary quotient module to an ambient finitely generated
right `A`-module. -/
def primitiveLeftInflateFGObj (e : A)
    (N : FGModuleCat.{u} (PrimitiveLeftQuotient e)) :
    FinitelyGeneratedCategory A := by
  let q := Ideal.Quotient.mk (primitiveLeftIdeal e).asIdeal
  let U := (ModuleCat.restrictScalars q).obj N.obj
  letI : Module.Finite k N := Module.Finite.trans (PrimitiveLeftQuotient e) N
  letI : Module.Finite k U := by
    exact Module.Finite.equiv
      (LeftModule.quotientRestrictLinearEquiv (primitiveLeftIdeal e) N.obj)
  letI : Module.Finite Aᵐᵒᵖ U :=
    Module.Finite.of_restrictScalars_finite k Aᵐᵒᵖ U
  exact ⟨U, show Module.Finite Aᵐᵒᵖ U from inferInstance⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Inflation along the auxiliary quotient is annihilated by `AeA`. -/
theorem primitiveLeftInflateFGObj_isAnnihilatedBy (e : A)
    (N : FGModuleCat.{u} (PrimitiveLeftQuotient e)) :
    IsAnnihilatedBy (primitiveIdeal e)
      (primitiveLeftInflateFGObj (k := k) e N) := by
  intro n a ha
  have hzero : ∀ x : N, (MulOpposite.op a) •
      (show primitiveLeftInflateFGObj (k := k) e N from x) = 0 := by
    intro x
    change (Ideal.Quotient.mk (primitiveLeftIdeal e).asIdeal
      (MulOpposite.op a)) • x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr, zero_smul]
    simpa [primitiveLeftIdeal] using ha
  exact hzero n

/-- Inflation along the auxiliary quotient, bundled in the annihilated full
subcategory. -/
def primitiveLeftInflateFunctor (e : A) :
    FGModuleCat.{u} (PrimitiveLeftQuotient e) ⥤
      PrimitiveQuotientSubcategory e where
  obj N := ⟨primitiveLeftInflateFGObj (k := k) e N,
    primitiveLeftInflateFGObj_isAnnihilatedBy (k := k) e N⟩
  map {M N} f := ObjectProperty.homMk <| ObjectProperty.homMk <|
    (ModuleCat.restrictScalars
      (Ideal.Quotient.mk (primitiveLeftIdeal e).asIdeal)).map f.hom
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- Inflation from the quotient preserves the preadditive structure. -/
noncomputable instance primitiveLeftInflateFunctorAdditive (e : A) :
    (primitiveLeftInflateFunctor (k := k) e).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- Inflation from the auxiliary quotient is linear over the ground field. -/
noncomputable instance primitiveLeftInflateFunctorLinear (e : A) :
    (primitiveLeftInflateFunctor (k := k) e).Linear k where
  map_smul := by
    intro M N f a
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- Unit component for the auxiliary primitive-quotient equivalence. -/
def primitiveLeftUnitIsoApp (e : A)
    (M : PrimitiveQuotientSubcategory e) :
    M ≅ (primitiveLeftFunctor (k := k) e ⋙
      primitiveLeftInflateFunctor (k := k) e).obj M :=
  ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
    (primitiveLeftObjRestrictIso e M.obj M.property).symm

/-- Counit component for the auxiliary primitive-quotient equivalence. -/
def primitiveLeftCounitIsoApp (e : A)
    (N : FGModuleCat.{u} (PrimitiveLeftQuotient e)) :
    (primitiveLeftInflateFunctor (k := k) e ⋙
      primitiveLeftFunctor (k := k) e).obj N ≅ N := by
  apply ObjectProperty.isoMk
  apply LeftModule.quotientRestrictIso (primitiveLeftIdeal e)
  exact primitiveLeftObjRestrictIso e
    (primitiveLeftInflateFGObj (k := k) e N)
    (primitiveLeftInflateFGObj_isAnnihilatedBy (k := k) e N)

/-- Modules over the auxiliary quotient are equivalent to annihilated
ambient modules. -/
def primitiveLeftEquivalence (e : A) :
    PrimitiveQuotientSubcategory e ≌ FGModuleCat.{u} (PrimitiveLeftQuotient e) where
  functor := primitiveLeftFunctor (k := k) e
  inverse := primitiveLeftInflateFunctor (k := k) e
  unitIso := NatIso.ofComponents (primitiveLeftUnitIsoApp (k := k) e) (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    ext m
    change f.hom m = f.hom m
    rfl)
  counitIso := NatIso.ofComponents (primitiveLeftCounitIsoApp (k := k) e) (by
    intro M N f
    apply ObjectProperty.hom_ext
    ext m
    change f m = f m
    rfl)

noncomputable instance primitiveLeftEquivalenceFunctorLinear (e : A) :
    (primitiveLeftEquivalence (k := k) e).functor.Linear k := by
  dsimp [primitiveLeftEquivalence]
  infer_instance

noncomputable instance primitiveLeftEquivalenceInverseLinear (e : A) :
    (primitiveLeftEquivalence (k := k) e).inverse.Linear k := by
  dsimp [primitiveLeftEquivalence]
  infer_instance

/-- Finitely generated right modules over the manuscript's literal
`A/AeA` are equivalent to the full ambient subcategory annihilated by
`AeA`. -/
def primitiveQuotientEquivalence (e : A) :
    PrimitiveQuotientSubcategory e ≌
      FinitelyGeneratedCategory (primitiveQuotientAlgebra e) :=
  (primitiveLeftEquivalence (k := k) e).trans
    (LeftModule.fgModuleEquivalenceOfAlgEquiv
      (primitiveLeftQuotientAlgEquiv (k := k) e))

/-- The literal primitive-quotient equivalence preserves addition on
morphisms. -/
noncomputable instance primitiveQuotientEquivalenceFunctorAdditive (e : A) :
    (primitiveQuotientEquivalence (k := k) e).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    rfl

/-- The inverse literal primitive-quotient equivalence preserves addition on
morphisms. -/
noncomputable instance primitiveQuotientEquivalenceInverseAdditive (e : A) :
    (primitiveQuotientEquivalence (k := k) e).inverse.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- The literal primitive-quotient equivalence is linear over the ground
field. -/
noncomputable instance primitiveQuotientEquivalenceFunctorLinear (e : A) :
    (primitiveQuotientEquivalence (k := k) e).functor.Linear k where
  map_smul := by
    intro M N f a
    change (LeftModule.fgModuleEquivalenceOfAlgEquiv
      (primitiveLeftQuotientAlgEquiv (k := k) e)).functor.map
        ((primitiveLeftEquivalence (k := k) e).functor.map (a • f)) = _
    rw [Functor.map_smul, Functor.map_smul]
    rfl

/-- The inverse literal primitive-quotient equivalence is linear over the
ground field. -/
noncomputable instance primitiveQuotientEquivalenceInverseLinear (e : A) :
    (primitiveQuotientEquivalence (k := k) e).inverse.Linear k where
  map_smul := by
    intro M N f a
    change (primitiveLeftEquivalence (k := k) e).inverse.map
      ((LeftModule.fgModuleEquivalenceOfAlgEquiv
        (primitiveLeftQuotientAlgEquiv (k := k) e)).inverse.map
          (a • f)) = _
    rw [Functor.map_smul, Functor.map_smul]
    rfl

/-- Epimorphisms in the annihilated full subcategory are already
epimorphisms of ambient finitely generated right modules. -/
theorem primitiveQuotientSubcategory_epi_ambient (e : A)
    {M N : PrimitiveQuotientSubcategory e}
    (f : M ⟶ N) [Epi f] : Epi f.hom := by
  apply
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      f.hom).2
  intro y
  let R : Submodule Aᵐᵒᵖ N.obj := LinearMap.range f.hom.hom.hom
  let Q : FinitelyGeneratedCategory A := FGModuleCat.of Aᵐᵒᵖ (N.obj ⧸ R)
  have hQ : IsAnnihilatedBy (primitiveIdeal e) Q := by
    rw [isAnnihilatedBy_primitiveIdeal_iff]
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have hx := (isAnnihilatedBy_primitiveIdeal_iff e N.obj).1 N.property x
      change Submodule.Quotient.mk (MulOpposite.op e • x) = 0
      rw [hx]
      rfl
  let Q' : PrimitiveQuotientSubcategory e := ⟨Q, hQ⟩
  let q : N.obj ⟶ Q := FGModuleCat.ofHom R.mkQ
  let q' : N ⟶ Q' := ObjectProperty.homMk q
  have hfq : f ≫ q' = 0 := by
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x
    change R.mkQ (f.hom x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  have hqzero : q' = 0 := by
    apply (cancel_epi f).1
    simpa using hfq
  have hyzero := congrArg (fun g ↦ g.hom.hom.hom y) hqzero
  change R.mkQ y = 0 at hyzero
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hyzero
  exact hyzero

omit [FiniteDimensional k A] in
/-- Representation-finiteness descends to the manuscript's literal
primitive quotient. -/
theorem primitiveQuotient_isRepresentationFinite
    (hA : IsRepresentationFinite k A) (e : A) :
    IsRepresentationFinite k (primitiveQuotientAlgebra e) := by
  have hleft : LeftModule.IsRepresentationFinite k Aᵐᵒᵖ := hA
  have hquot : LeftModule.IsRepresentationFinite k (PrimitiveLeftQuotient e) :=
    LeftModule.IsRepresentationFinite.quotient hleft (primitiveLeftIdeal e)
  exact hquot.of_algEquiv (primitiveLeftQuotientAlgEquiv (k := k) e)

end MagnitudeConjecture.RightModule
