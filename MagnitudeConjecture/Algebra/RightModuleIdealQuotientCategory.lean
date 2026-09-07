import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotient
import MagnitudeConjecture.Algebra.RepresentationFiniteQuotient
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Right modules over an arbitrary two-sided quotient

For a two-sided ideal `I ⊆ A`, finitely generated right modules over `A/I`
are the same as finitely generated right `A`-modules annihilated by `I`.
Mathlib's quotient-module API is phrased for left modules, so the construction
first uses the quotient of `Aᵐᵒᵖ` by `I.op` and then transports across the
canonical algebra equivalence with `(A/I)ᵐᵒᵖ`.

This is the ideal-independent categorical boundary needed for socle
rejection.  It also isolates the common part of the existing primitive and
support quotient constructions without imposing either of their additional
combinatorial hypotheses.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The opposite ideal through which right modules annihilated by `I`
acquire their quotient action. -/
def idealLeftIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal Aᵐᵒᵖ := I.op

/-- The auxiliary quotient acting on the left on right `A`-modules. -/
abbrev IdealLeftQuotient (I : TwoSidedIdeal A) :=
  Aᵐᵒᵖ ⧸ (idealLeftIdeal I).asIdeal

/-- The literal quotient algebra `A/I`. -/
abbrev idealQuotientAlgebra (I : TwoSidedIdeal A) := I.ringCon.Quotient

/-- The canonical algebra map `A ⟶ A/I`. -/
def idealQuotientAlgMap (I : TwoSidedIdeal A) :
    A →ₐ[k] idealQuotientAlgebra I :=
  I.ringCon.mkₐ k

/-- The opposite quotient map used to inflate right `A/I`-modules. -/
def idealQuotientOpAlgMap (I : TwoSidedIdeal A) :
    Aᵐᵒᵖ →ₐ[k] (idealQuotientAlgebra I)ᵐᵒᵖ :=
  (idealQuotientAlgMap (k := k) I).op

omit [FiniteDimensional k A] in
theorem idealQuotientOpAlgMap_ker (I : TwoSidedIdeal A) :
    RingHom.ker (idealQuotientOpAlgMap (k := k) I) =
      (idealLeftIdeal I).asIdeal := by
  ext a
  rw [RingHom.mem_ker, TwoSidedIdeal.mem_asIdeal,
    idealLeftIdeal, TwoSidedIdeal.mem_op_iff]
  change MulOpposite.op (I.ringCon.mk' a.unop) = MulOpposite.op 0 ↔
    a.unop ∈ I
  rw [MulOpposite.op_inj, ← TwoSidedIdeal.mem_ker,
    TwoSidedIdeal.ker_ringCon_mk']

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem idealQuotientOpAlgMap_surjective (I : TwoSidedIdeal A) :
    Function.Surjective (idealQuotientOpAlgMap (k := k) I) := by
  intro b
  obtain ⟨a, ha⟩ := RingCon.mkₐ_surjective (α := k) I.ringCon b.unop
  refine ⟨MulOpposite.op a, ?_⟩
  apply MulOpposite.unop_injective
  exact ha

/-- The quotient of `Aᵐᵒᵖ` by `I.op` is canonically the opposite of
the literal quotient `A/I`. -/
def idealLeftQuotientAlgEquiv (I : TwoSidedIdeal A) :
    IdealLeftQuotient I ≃ₐ[k] (idealQuotientAlgebra I)ᵐᵒᵖ :=
  (Ideal.quotientEquivAlgOfEq k
      (idealQuotientOpAlgMap_ker (k := k) I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (idealQuotientOpAlgMap_surjective (k := k) I))

noncomputable instance idealLeftQuotientModuleFinite (I : TwoSidedIdeal A) :
    Module.Finite k (IdealLeftQuotient I) := by
  infer_instance

noncomputable instance idealQuotientOpModuleFinite (I : TwoSidedIdeal A) :
    Module.Finite k (idealQuotientAlgebra I)ᵐᵒᵖ :=
  Module.Finite.equiv (idealLeftQuotientAlgEquiv (k := k) I).toLinearEquiv

noncomputable instance idealQuotientModuleFinite (I : TwoSidedIdeal A) :
    Module.Finite k (idealQuotientAlgebra I) :=
  Module.Finite.equiv
    (MulOpposite.opLinearEquiv k :
      idealQuotientAlgebra I ≃ₗ[k] (idealQuotientAlgebra I)ᵐᵒᵖ).symm

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- An ambient right module annihilated by `I` is a module over the
auxiliary quotient of `Aᵐᵒᵖ`. -/
theorem isTorsionByIdealLeftIdeal (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) (hM : IsAnnihilatedBy I M) :
    Module.IsTorsionBySet Aᵐᵒᵖ M (idealLeftIdeal I).asIdeal := by
  intro m a
  exact hM m a.1.unop (by simpa [idealLeftIdeal] using a.2)

/-- The full subcategory of ambient right modules annihilated by `I`. -/
def IdealQuotientProperty (I : TwoSidedIdeal A) :
    ObjectProperty (FinitelyGeneratedCategory A) :=
  fun M ↦ IsAnnihilatedBy I M

omit [FiniteDimensional k A] in
/-- Annihilation by a two-sided ideal is inherited by subobjects. -/
instance idealQuotientProperty_closedUnderSubobjects (I : TwoSidedIdeal A) :
    (IdealQuotientProperty I).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    have hinjective : Function.Injective f :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective
        f).1 inferInstance
    intro x a ha
    apply hinjective
    have hzero := hY (f x) a ha
    simpa only [map_smul, map_zero] using hzero

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- Annihilation by a two-sided ideal is inherited by direct summands. -/
instance idealQuotientProperty_stableUnderRetracts (I : TwoSidedIdeal A) :
    (IdealQuotientProperty I).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    change IsAnnihilatedBy I Y at hY
    change IsAnnihilatedBy I X
    intro x a ha
    have hzero := hY (r.i x) a ha
    apply_fun r.r at hzero
    have hri : r.r (r.i x) = x := by
      have h := congrArg (fun f : X ⟶ X ↦ f.hom.hom x) r.retract
      change r.r.hom.hom (r.i.hom.hom x) = x at h
      exact h
    simpa only [map_smul, map_zero, hri] using hzero

/-- The ambient realization of the finitely generated right `A/I`-module
category. -/
abbrev IdealQuotientSubcategory (I : TwoSidedIdeal A) :=
  (IdealQuotientProperty I).FullSubcategory

/-- An annihilated ambient module, regarded as a module over the auxiliary
left quotient. -/
def idealLeftObj (I : TwoSidedIdeal A) (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy I M) : ModuleCat (IdealLeftQuotient I) := by
  let htor := isTorsionByIdealLeftIdeal I M hM
  letI : Module (IdealLeftQuotient I) M := htor.module
  exact ModuleCat.of (IdealLeftQuotient I) M

/-- Passing to the auxiliary quotient does not change the underlying
finite-dimensional `k`-vector space. -/
def idealLeftObjLinearEquiv (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) (hM : IsAnnihilatedBy I M) :
    M ≃ₗ[k] idealLeftObj I M hM := by
  let htor := isTorsionByIdealLeftIdeal I M hM
  letI : Module (IdealLeftQuotient I) M := htor.module
  change M ≃ₗ[k] ModuleCat.of (IdealLeftQuotient I) M
  exact {
    toFun := fun m ↦ m
    invFun := fun m ↦ m
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := by
      intro c m
      change c • m =
        (Ideal.Quotient.mk (idealLeftIdeal I).asIdeal
          (algebraMap k Aᵐᵒᵖ c)) • m
      exact (htor.mk_smul (algebraMap k Aᵐᵒᵖ c) m).symm }

/-- Restriction from the auxiliary quotient recovers the original ambient
module by the identity on its carrier. -/
def idealLeftObjRestrictIso (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) (hM : IsAnnihilatedBy I M) :
    (ModuleCat.restrictScalars
      (Ideal.Quotient.mk (idealLeftIdeal I).asIdeal)).obj
        (idealLeftObj I M hM) ≅ M.obj := by
  let htor := isTorsionByIdealLeftIdeal I M hM
  letI : Module (IdealLeftQuotient I) M := htor.module
  change (ModuleCat.restrictScalars
    (Ideal.Quotient.mk (idealLeftIdeal I).asIdeal)).obj
      (ModuleCat.of (IdealLeftQuotient I) M) ≅ M.obj
  exact LinearEquiv.toModuleIso {
    toFun := fun m ↦ m
    invFun := fun m ↦ m
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun a m ↦ htor.mk_smul a m }

/-- Every ambient morphism between annihilated modules is linear over the
auxiliary quotient. -/
def idealLeftMap (I : TwoSidedIdeal A)
    (M N : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy I M) (hN : IsAnnihilatedBy I N)
    (f : M ⟶ N) : idealLeftObj I M hM ⟶ idealLeftObj I N hN := by
  let hMtor := isTorsionByIdealLeftIdeal I M hM
  let hNtor := isTorsionByIdealLeftIdeal I N hN
  letI : Module (IdealLeftQuotient I) M := hMtor.module
  letI : Module (IdealLeftQuotient I) N := hNtor.module
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
theorem idealLeftMap_apply (I : TwoSidedIdeal A)
    (M N : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy I M) (hN : IsAnnihilatedBy I N)
    (f : M ⟶ N) (m : M) :
    idealLeftMap I M N hM hN f m = f m := rfl

/-- The quotient object bundled in the finitely generated module category. -/
def idealLeftFGObj (I : TwoSidedIdeal A) (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy I M) : FGModuleCat.{u} (IdealLeftQuotient I) := by
  letI : Module.Finite k (idealLeftObj I M hM) := by
    letI : Module.Finite k M :=
      finite_over_field_of_finitelyGenerated k A M
    exact Module.Finite.equiv (idealLeftObjLinearEquiv I M hM)
  letI : Module.Finite (IdealLeftQuotient I) (idealLeftObj I M hM) :=
    Module.Finite.of_restrictScalars_finite k (IdealLeftQuotient I)
      (idealLeftObj I M hM)
  exact FGModuleCat.of (IdealLeftQuotient I) (idealLeftObj I M hM)

/-- Passage from the annihilated ambient subcategory to modules over the
auxiliary quotient. -/
def idealLeftFunctor (I : TwoSidedIdeal A) :
    IdealQuotientSubcategory I ⥤ FGModuleCat.{u} (IdealLeftQuotient I) where
  obj M := idealLeftFGObj (k := k) I M.obj M.property
  map {M N} f := ObjectProperty.homMk
    (idealLeftMap I M.obj N.obj M.property N.property f.hom)
  map_id M := by
    apply FGModuleCat.hom_ext
    ext m
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    ext m
    rfl

noncomputable instance idealLeftFunctorAdditive (I : TwoSidedIdeal A) :
    (idealLeftFunctor (k := k) I).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    rfl

noncomputable instance idealLeftFunctorLinear (I : TwoSidedIdeal A) :
    (idealLeftFunctor (k := k) I).Linear k where
  map_smul := by
    intro M N f a
    apply ObjectProperty.hom_ext
    rfl

/-- Inflate an auxiliary quotient module to an ambient finitely generated
right `A`-module. -/
def idealLeftInflateFGObj (I : TwoSidedIdeal A)
    (N : FGModuleCat.{u} (IdealLeftQuotient I)) :
    FinitelyGeneratedCategory A := by
  let q := Ideal.Quotient.mk (idealLeftIdeal I).asIdeal
  let U := (ModuleCat.restrictScalars q).obj N.obj
  letI : Module.Finite k N := Module.Finite.trans (IdealLeftQuotient I) N
  letI : Module.Finite k U := by
    exact Module.Finite.equiv
      (LeftModule.quotientRestrictLinearEquiv (idealLeftIdeal I) N.obj)
  letI : Module.Finite Aᵐᵒᵖ U :=
    Module.Finite.of_restrictScalars_finite k Aᵐᵒᵖ U
  exact ⟨U, show Module.Finite Aᵐᵒᵖ U from inferInstance⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Inflation along the auxiliary quotient is annihilated by `I`. -/
theorem idealLeftInflateFGObj_isAnnihilatedBy (I : TwoSidedIdeal A)
    (N : FGModuleCat.{u} (IdealLeftQuotient I)) :
    IsAnnihilatedBy I (idealLeftInflateFGObj (k := k) I N) := by
  intro n a ha
  have hzero : ∀ x : N, (MulOpposite.op a) •
      (show idealLeftInflateFGObj (k := k) I N from x) = 0 := by
    intro x
    change (Ideal.Quotient.mk (idealLeftIdeal I).asIdeal
      (MulOpposite.op a)) • x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr, zero_smul]
    simpa [idealLeftIdeal] using ha
  exact hzero n

/-- Inflation along the quotient, bundled in the annihilated full
subcategory. -/
def idealLeftInflateFunctor (I : TwoSidedIdeal A) :
    FGModuleCat.{u} (IdealLeftQuotient I) ⥤ IdealQuotientSubcategory I where
  obj N := ⟨idealLeftInflateFGObj (k := k) I N,
    idealLeftInflateFGObj_isAnnihilatedBy (k := k) I N⟩
  map {M N} f := ObjectProperty.homMk <| ObjectProperty.homMk <|
    (ModuleCat.restrictScalars
      (Ideal.Quotient.mk (idealLeftIdeal I).asIdeal)).map f.hom
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

noncomputable instance idealLeftInflateFunctorAdditive (I : TwoSidedIdeal A) :
    (idealLeftInflateFunctor (k := k) I).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

noncomputable instance idealLeftInflateFunctorLinear (I : TwoSidedIdeal A) :
    (idealLeftInflateFunctor (k := k) I).Linear k where
  map_smul := by
    intro M N f a
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- Unit component of the arbitrary ideal-quotient equivalence. -/
def idealLeftUnitIsoApp (I : TwoSidedIdeal A) (M : IdealQuotientSubcategory I) :
    M ≅ (idealLeftFunctor (k := k) I ⋙
      idealLeftInflateFunctor (k := k) I).obj M :=
  ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
    (idealLeftObjRestrictIso I M.obj M.property).symm

/-- Counit component of the arbitrary ideal-quotient equivalence. -/
def idealLeftCounitIsoApp (I : TwoSidedIdeal A)
    (N : FGModuleCat.{u} (IdealLeftQuotient I)) :
    (idealLeftInflateFunctor (k := k) I ⋙
      idealLeftFunctor (k := k) I).obj N ≅ N := by
  apply ObjectProperty.isoMk
  apply LeftModule.quotientRestrictIso (idealLeftIdeal I)
  exact idealLeftObjRestrictIso I
    (idealLeftInflateFGObj (k := k) I N)
    (idealLeftInflateFGObj_isAnnihilatedBy (k := k) I N)

/-- Modules over the auxiliary quotient are equivalent to annihilated
ambient modules. -/
def idealLeftEquivalence (I : TwoSidedIdeal A) :
    IdealQuotientSubcategory I ≌ FGModuleCat.{u} (IdealLeftQuotient I) where
  functor := idealLeftFunctor (k := k) I
  inverse := idealLeftInflateFunctor (k := k) I
  unitIso := NatIso.ofComponents (idealLeftUnitIsoApp (k := k) I) (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    ext m
    change f.hom m = f.hom m
    rfl)
  counitIso := NatIso.ofComponents (idealLeftCounitIsoApp (k := k) I) (by
    intro M N f
    apply ObjectProperty.hom_ext
    ext m
    change f m = f m
    rfl)

noncomputable instance idealLeftEquivalenceFunctorLinear (I : TwoSidedIdeal A) :
    (idealLeftEquivalence (k := k) I).functor.Linear k := by
  dsimp [idealLeftEquivalence]
  infer_instance

noncomputable instance idealLeftEquivalenceInverseLinear (I : TwoSidedIdeal A) :
    (idealLeftEquivalence (k := k) I).inverse.Linear k := by
  dsimp [idealLeftEquivalence]
  infer_instance

/-- Finitely generated right modules over `A/I` are equivalent to the full
ambient subcategory annihilated by `I`. -/
def idealQuotientEquivalence (I : TwoSidedIdeal A) :
    IdealQuotientSubcategory I ≌ FinitelyGeneratedCategory (idealQuotientAlgebra I) :=
  (idealLeftEquivalence (k := k) I).trans
    (LeftModule.fgModuleEquivalenceOfAlgEquiv
      (idealLeftQuotientAlgEquiv (k := k) I))

noncomputable instance idealQuotientEquivalenceFunctorAdditive
    (I : TwoSidedIdeal A) :
    (idealQuotientEquivalence (k := k) I).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    rfl

noncomputable instance idealQuotientEquivalenceInverseAdditive
    (I : TwoSidedIdeal A) :
    (idealQuotientEquivalence (k := k) I).inverse.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

noncomputable instance idealQuotientEquivalenceFunctorLinear
    (I : TwoSidedIdeal A) :
    (idealQuotientEquivalence (k := k) I).functor.Linear k where
  map_smul := by
    intro M N f a
    change (LeftModule.fgModuleEquivalenceOfAlgEquiv
      (idealLeftQuotientAlgEquiv (k := k) I)).functor.map
        ((idealLeftEquivalence (k := k) I).functor.map (a • f)) = _
    rw [Functor.map_smul, Functor.map_smul]
    rfl

noncomputable instance idealQuotientEquivalenceInverseLinear
    (I : TwoSidedIdeal A) :
    (idealQuotientEquivalence (k := k) I).inverse.Linear k where
  map_smul := by
    intro M N f a
    change (idealLeftEquivalence (k := k) I).inverse.map
      ((LeftModule.fgModuleEquivalenceOfAlgEquiv
        (idealLeftQuotientAlgEquiv (k := k) I)).inverse.map (a • f)) = _
    rw [Functor.map_smul, Functor.map_smul]
    rfl

/-- Epimorphisms in the annihilated full subcategory are already
epimorphisms of ambient finitely generated right modules. -/
theorem idealQuotientSubcategory_epi_ambient (I : TwoSidedIdeal A)
    {M N : IdealQuotientSubcategory I} (f : M ⟶ N) [Epi f] : Epi f.hom := by
  apply
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      f.hom).2
  intro y
  let R : Submodule Aᵐᵒᵖ N.obj := LinearMap.range f.hom.hom.hom
  let Q : FinitelyGeneratedCategory A := FGModuleCat.of Aᵐᵒᵖ (N.obj ⧸ R)
  have hQ : IsAnnihilatedBy I Q := by
    intro x a ha
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have hx := N.property x a ha
      change Submodule.Quotient.mk (MulOpposite.op a • x) = 0
      rw [hx]
      rfl
  let Q' : IdealQuotientSubcategory I := ⟨Q, hQ⟩
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
/-- Representation-finiteness descends to every literal two-sided
quotient. -/
theorem idealQuotient_isRepresentationFinite
    (hA : IsRepresentationFinite k A) (I : TwoSidedIdeal A) :
    IsRepresentationFinite k (idealQuotientAlgebra I) := by
  have hleft : LeftModule.IsRepresentationFinite k Aᵐᵒᵖ := hA
  have hquot : LeftModule.IsRepresentationFinite k (IdealLeftQuotient I) :=
    LeftModule.IsRepresentationFinite.quotient hleft (idealLeftIdeal I)
  exact hquot.of_algEquiv (idealLeftQuotientAlgEquiv (k := k) I)

end MagnitudeConjecture.RightModule
