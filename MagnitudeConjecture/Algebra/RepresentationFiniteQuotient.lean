import MagnitudeConjecture.Algebra.RightModuleFiniteType
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Representation-finiteness of algebra quotients

Restriction along a quotient map realizes quotient modules as the full exact
subcategory annihilated by the quotient ideal.  In particular,
representation-finiteness descends to every two-sided quotient.  We also
record the small algebra-equivalence transport needed to return from left
modules over the quotient of an opposite algebra to right modules.

The proofs are adapted from
`CartanDeterminant.Algebra.RepresentationFinite` and
`CartanDeterminant.Algebra.RepresentationFiniteIdeals` at
homological-conjectures commit `916afb44`; the unrelated ideal-lattice and
representation-infinite applications are omitted.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.LeftModule

universe u v w

variable (k : Type u) [Field k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- A finite-dimensional indecomposable left module. -/
def IsFiniteIndecomposable (M : ModuleCat.{v} A) : Prop :=
  Module.Finite k M ∧ Indecomposable M

/-- Finiteness of the isomorphism classes of finite-dimensional
indecomposable left modules. -/
def IsRepresentationFinite : Prop :=
  ∃ n : ℕ, ∃ X : Fin n → ModuleCat.{v} A,
    (∀ i, IsFiniteIndecomposable k A (X i)) ∧
      ∀ M : ModuleCat.{v} A, IsFiniteIndecomposable k A M →
        ∃ i, Nonempty (M ≅ X i)

private theorem indecomposable_iff_of_iso
    {C : Type v} [Category.{w} C] [Preadditive C]
    [HasBinaryBiproducts C] {X Y : C} (e : X ≅ Y) :
    Indecomposable X ↔ Indecomposable Y := by
  constructor
  · rintro ⟨hX0, hX⟩
    refine ⟨?_, ?_⟩
    · intro hY0
      exact hX0 ((e.isZero_iff).2 hY0)
    · intro Z W hYW
      exact hX Z W (e.trans hYW)
  · rintro ⟨hY0, hY⟩
    refine ⟨?_, ?_⟩
    · intro hX0
      exact hY0 ((e.isZero_iff).1 hX0)
    · intro Z W hXW
      exact hY Z W (e.symm.trans hXW)

/-- An additive equivalence preserves and reflects indecomposability. -/
theorem indecomposable_functor_obj_iff
    {C : Type v} [Category.{w} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {D : Type v} [Category.{w} D] [Preadditive D]
    [HasBinaryBiproducts D]
    (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive] (X : C) :
    Indecomposable (E.functor.obj X) ↔ Indecomposable X := by
  letI : PreservesBinaryBiproducts E.functor :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E.functor
  letI : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E.inverse
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hX0
      exact h.1 (E.functor.map_isZero hX0)
    · intro Y Z i
      let i' : E.functor.obj X ≅ E.functor.obj Y ⊞ E.functor.obj Z :=
        (E.functor.mapIso i).trans (E.functor.mapBiprod _ _)
      rcases h.2 _ _ i' with hY | hZ
      · exact Or.inl <| (E.unitIso.app Y).isZero_iff.mpr
          (E.inverse.map_isZero hY)
      · exact Or.inr <| (E.unitIso.app Z).isZero_iff.mpr
          (E.inverse.map_isZero hZ)
  · intro h
    refine ⟨?_, ?_⟩
    · intro hFX0
      exact h.1 ((E.unitIso.app X).isZero_iff.mpr
        (E.inverse.map_isZero hFX0))
    · intro Y Z i
      let i' : X ≅ E.inverse.obj Y ⊞ E.inverse.obj Z :=
        (E.unitIso.app X).trans ((E.inverse.mapIso i).trans
          (E.inverse.mapBiprod _ _))
      rcases h.2 _ _ i' with hY | hZ
      · exact Or.inl <| (E.counitIso.app Y).isZero_iff.mp
          (E.functor.map_isZero hY)
      · exact Or.inr <| (E.counitIso.app Z).isZero_iff.mp
          (E.functor.map_isZero hZ)

private theorem moduleFinite_iff_of_iso
    {M N : ModuleCat.{v} A} (e : M ≅ N) :
    Module.Finite k M ↔ Module.Finite k N := by
  let e' : M ≃ₗ[k] N := (e.toLinearEquiv).restrictScalars k
  exact Module.Finite.equiv_iff e'

variable {k A}
variable {B : Type v} [Ring B] [Algebra k B]

private theorem IsRepresentationFinite.of_equivalence
    (hA : IsRepresentationFinite k A)
    (E : ModuleCat.{v} A ≌ ModuleCat.{v} B)
    [E.functor.Additive] [E.inverse.Additive]
    (hfinite : ∀ M : ModuleCat.{v} A,
      Module.Finite k M ↔ Module.Finite k (E.functor.obj M)) :
    IsRepresentationFinite k B := by
  obtain ⟨n, X, hX, hcover⟩ := hA
  refine ⟨n, fun i ↦ E.functor.obj (X i), ?_, ?_⟩
  · intro i
    exact ⟨(hfinite (X i)).mp (hX i).1,
      (indecomposable_functor_obj_iff E (X i)).mpr (hX i).2⟩
  · intro M hM
    have hFGMfinite : Module.Finite k
        (E.functor.obj (E.inverse.obj M)) :=
      (moduleFinite_iff_of_iso k B (E.counitIso.app M)).mpr hM.1
    have hGMfinite : Module.Finite k (E.inverse.obj M) :=
      (hfinite (E.inverse.obj M)).mpr hFGMfinite
    have hFGMind : Indecomposable
        (E.functor.obj (E.inverse.obj M)) :=
      (indecomposable_iff_of_iso (E.counitIso.app M)).mpr hM.2
    have hGMind : Indecomposable (E.inverse.obj M) :=
      (indecomposable_functor_obj_iff E (E.inverse.obj M)).mp hFGMind
    obtain ⟨i, ⟨e⟩⟩ := hcover (E.inverse.obj M) ⟨hGMfinite, hGMind⟩
    exact ⟨i, ⟨(E.counitIso.app M).symm.trans (E.functor.mapIso e)⟩⟩

/-- The module-category equivalence induced by an algebra equivalence. -/
abbrev moduleEquivalenceOfAlgEquiv (f : A ≃ₐ[k] B) :
    ModuleCat.{v} A ≌ ModuleCat.{v} B :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv

/-- The underlying `k`-linear equivalence from a module to its image under
the equivalence induced by an algebra equivalence. -/
def moduleEquivalenceOfAlgEquivObjLinearEquiv
    (f : A ≃ₐ[k] B) (M : ModuleCat.{v} A) :
    M ≃ₗ[k] (moduleEquivalenceOfAlgEquiv f).functor.obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    exact congrArg (fun a : A ↦ a • x) (f.symm.commutes c).symm

/-- An algebra equivalence induces an equivalence between the literal
categories of finitely generated modules.  Finite-dimensionality of the two
algebras over `k` supplies finite generation after each restriction of
scalars. -/
def fgModuleEquivalenceOfAlgEquiv
    [Module.Finite k A] [Module.Finite k B]
    (f : A ≃ₐ[k] B) :
    FGModuleCat.{v} A ≌ FGModuleCat.{v} B := by
  let E := moduleEquivalenceOfAlgEquiv f
  letI : (ModuleCat.isFG.{v} B).IsClosedUnderIsomorphisms := by
    constructor
    intro X Y e hX
    letI : Module.Finite B X := hX
    exact Module.Finite.equiv e.toLinearEquiv
  apply E.congrFullSubcategory
  funext M
  apply propext
  constructor
  · intro hM
    letI : Module.Finite B (E.functor.obj M) := hM
    letI : Module.Finite k (E.functor.obj M) :=
      Module.Finite.trans B (E.functor.obj M)
    letI : Module.Finite k M := Module.Finite.equiv
      (moduleEquivalenceOfAlgEquivObjLinearEquiv f M).symm
    exact Module.Finite.of_restrictScalars_finite k A M
  · intro hM
    letI : Module.Finite A M := hM
    letI : Module.Finite k M := Module.Finite.trans A M
    letI : Module.Finite k (E.functor.obj M) :=
      Module.Finite.equiv
        (moduleEquivalenceOfAlgEquivObjLinearEquiv f M)
    exact Module.Finite.of_restrictScalars_finite k B (E.functor.obj M)

noncomputable instance fgModuleEquivalenceOfAlgEquivFunctorAdditive
    [Module.Finite k A] [Module.Finite k B]
    (f : A ≃ₐ[k] B) :
    (fgModuleEquivalenceOfAlgEquiv f).functor.Additive where
  map_add := by
    intro X Y g h
    apply ObjectProperty.hom_ext
    rfl

noncomputable instance fgModuleEquivalenceOfAlgEquivInverseAdditive
    [Module.Finite k A] [Module.Finite k B]
    (f : A ≃ₐ[k] B) :
    (fgModuleEquivalenceOfAlgEquiv f).inverse.Additive where
  map_add := by
    intro X Y g h
    apply ObjectProperty.hom_ext
    rfl

/-- Restriction along an algebra equivalence is linear over the common
ground field. -/
noncomputable instance fgModuleEquivalenceOfAlgEquivFunctorLinear
    [Module.Finite k A] [Module.Finite k B]
    (f : A ≃ₐ[k] B) :
    (fgModuleEquivalenceOfAlgEquiv f).functor.Linear k where
  map_smul := by
    intro M N g a
    apply ObjectProperty.hom_ext
    ext x
    change (moduleEquivalenceOfAlgEquivObjLinearEquiv f N.obj) (a • g x) =
      a • (moduleEquivalenceOfAlgEquivObjLinearEquiv f N.obj) (g x)
    exact (moduleEquivalenceOfAlgEquivObjLinearEquiv f N.obj).map_smul a (g x)

/-- The inverse restriction equivalence is linear over the common ground
field. -/
noncomputable instance fgModuleEquivalenceOfAlgEquivInverseLinear
    [Module.Finite k A] [Module.Finite k B]
    (f : A ≃ₐ[k] B) :
    (fgModuleEquivalenceOfAlgEquiv f).inverse.Linear k where
  map_smul := by
    intro M N g a
    apply ObjectProperty.hom_ext
    ext x
    change (moduleEquivalenceOfAlgEquivObjLinearEquiv f.symm N.obj) (a • g x) =
      a • (moduleEquivalenceOfAlgEquivObjLinearEquiv f.symm N.obj) (g x)
    exact (moduleEquivalenceOfAlgEquivObjLinearEquiv f.symm N.obj).map_smul a (g x)

/-- Representation-finiteness is preserved by an algebra equivalence. -/
theorem IsRepresentationFinite.of_algEquiv
    (hA : IsRepresentationFinite k A) (f : A ≃ₐ[k] B) :
    IsRepresentationFinite k B := by
  apply IsRepresentationFinite.of_equivalence hA
    (moduleEquivalenceOfAlgEquiv f)
  intro M
  exact Module.Finite.equiv_iff
    (moduleEquivalenceOfAlgEquivObjLinearEquiv f M)

/-- Indecomposability in the literal finitely generated module category is
equivalent to indecomposability of the underlying module. -/
theorem fgModule_indecomposable_iff_obj
    {R : Type v} [Ring R] [IsNoetherianRing R]
    (M : FGModuleCat.{v} R) :
    Indecomposable M ↔ Indecomposable M.obj := by
  let U := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  letI : U.Additive := ⟨by intros; rfl⟩
  constructor
  · intro hM
    refine ⟨?_, ?_⟩
    · intro hzero
      exact hM.1 (IsZero.of_full_of_faithful_of_isZero U M hzero)
    · intro Y Z e
      let pY : M.obj ⟶ Y := e.hom ≫ biprod.fst
      let pZ : M.obj ⟶ Z := e.hom ≫ biprod.snd
      letI : Module.Finite R Y :=
        Module.Finite.of_surjective pY.hom
          ((ModuleCat.epi_iff_surjective pY).mp inferInstance)
      letI : Module.Finite R Z :=
        Module.Finite.of_surjective pZ.hom
          ((ModuleCat.epi_iff_surjective pZ).mp inferInstance)
      let Yfg : FGModuleCat.{v} R :=
        ⟨Y, show Module.Finite R Y from inferInstance⟩
      let Zfg : FGModuleCat.{v} R :=
        ⟨Z, show Module.Finite R Z from inferInstance⟩
      letI : PreservesBinaryBiproduct Yfg Zfg U :=
        preservesBinaryBiproduct_of_preservesBinaryProduct U
      let efg : M ≅ Yfg ⊞ Zfg :=
        ObjectProperty.isoMk _
          (e.trans (U.mapBiprod Yfg Zfg).symm)
      rcases hM.2 Yfg Zfg efg with hY | hZ
      · have hYu := U.map_isZero hY
        change IsZero Y at hYu
        exact Or.inl hYu
      · have hZu := U.map_isZero hZ
        change IsZero Z at hZu
        exact Or.inr hZu
  · intro hM
    refine ⟨?_, ?_⟩
    · intro hzero
      exact hM.1 (U.map_isZero hzero)
    · intro Y Z e
      letI : PreservesBinaryBiproduct Y Z U :=
        preservesBinaryBiproduct_of_preservesBinaryProduct U
      let eUnderlying : M.obj ≅ U.obj Y ⊞ U.obj Z :=
        (U.mapIso e).trans (U.mapBiprod Y Z)
      rcases hM.2 (U.obj Y) (U.obj Z) eUnderlying with hY | hZ
      · exact Or.inl (IsZero.of_full_of_faithful_of_isZero U Y hY)
      · exact Or.inr (IsZero.of_full_of_faithful_of_isZero U Z hZ)

/-- Restriction along a quotient map preserves the underlying `k`-vector
space. -/
def quotientRestrictLinearEquiv (I : TwoSidedIdeal A)
    (M : ModuleCat.{v} (A ⧸ I.asIdeal)) :
    M ≃ₗ[k] (ModuleCat.restrictScalars
      (Ideal.Quotient.mk I.asIdeal)).obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k (A ⧸ I.asIdeal) c) • x =
      Ideal.Quotient.mk I.asIdeal (algebraMap k A c) • x
    rfl

/-- A map between quotient modules which is linear after restriction is
already linear over the quotient, because the quotient map is surjective. -/
def quotientRestrictLift (I : TwoSidedIdeal A)
    {M N : ModuleCat.{v} (A ⧸ I.asIdeal)}
    (g : (ModuleCat.restrictScalars
        (Ideal.Quotient.mk I.asIdeal)).obj M ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk I.asIdeal)).obj N) : M ⟶ N :=
  ModuleCat.ofHom {
    toFun := g
    map_add' := g.hom.map_add
    map_smul' := by
      intro b x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact g.hom.map_smul a x }

/-- An isomorphism between restricted quotient modules lifts uniquely to an
isomorphism over the quotient. -/
def quotientRestrictIso (I : TwoSidedIdeal A)
    {M N : ModuleCat.{v} (A ⧸ I.asIdeal)}
    (e : (ModuleCat.restrictScalars
        (Ideal.Quotient.mk I.asIdeal)).obj M ≅
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk I.asIdeal)).obj N) : M ≅ N where
  hom := quotientRestrictLift I e.hom
  inv := quotientRestrictLift I e.inv
  hom_inv_id := by
    ext x
    change e.inv (e.hom x) = x
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp e.hom_inv_id) x
  inv_hom_id := by
    ext x
    change e.hom (e.inv x) = x
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp e.inv_hom_id) x

@[simp]
theorem quotientRestrictIso_hom_apply (I : TwoSidedIdeal A)
    {M N : ModuleCat.{v} (A ⧸ I.asIdeal)}
    (e : (ModuleCat.restrictScalars
        (Ideal.Quotient.mk I.asIdeal)).obj M ≅
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk I.asIdeal)).obj N) (m : M) :
    (quotientRestrictIso I e).hom m = e.hom m := rfl

/-- Restriction along a quotient map preserves indecomposability. -/
theorem quotientRestrict_indecomposable (I : TwoSidedIdeal A)
    (M : ModuleCat.{v} (A ⧸ I.asIdeal)) (hM : Indecomposable M) :
    Indecomposable ((ModuleCat.restrictScalars
      (Ideal.Quotient.mk I.asIdeal)).obj M) := by
  let q := Ideal.Quotient.mk I.asIdeal
  constructor
  · intro hzero
    apply hM.1
    rw [ModuleCat.isZero_iff_subsingleton] at hzero ⊢
    exact hzero
  · intro Y Z e
    let pY : Y ⟶ (ModuleCat.restrictScalars q).obj M :=
      biprod.inl ≫ e.inv
    let rY : (ModuleCat.restrictScalars q).obj M ⟶ Y :=
      e.hom ≫ biprod.fst
    have hpYrY : pY ≫ rY = 𝟙 Y := by simp [pY, rY, Category.assoc]
    have hleftY : Function.LeftInverse rY pY := by
      intro y
      change (pY ≫ rY) y = y
      rw [hpYrY]
      rfl
    let pZ : Z ⟶ (ModuleCat.restrictScalars q).obj M :=
      biprod.inr ≫ e.inv
    let rZ : (ModuleCat.restrictScalars q).obj M ⟶ Z :=
      e.hom ≫ biprod.snd
    have hpZrZ : pZ ≫ rZ = 𝟙 Z := by simp [pZ, rZ, Category.assoc]
    have hleftZ : Function.LeftInverse rZ pZ := by
      intro z
      change (pZ ≫ rZ) z = z
      rw [hpZrZ]
      rfl
    have hYtors : Module.IsTorsionBySet A Y I.asIdeal := by
      intro y a
      apply hleftY.injective
      change pY (a.1 • y) = pY 0
      rw [map_smul, map_zero]
      change q a.1 • pY y = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.2, zero_smul]
    have hZtors : Module.IsTorsionBySet A Z I.asIdeal := by
      intro z a
      apply hleftZ.injective
      change pZ (a.1 • z) = pZ 0
      rw [map_smul, map_zero]
      change q a.1 • pZ z = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.2, zero_smul]
    letI : Module (A ⧸ I.asIdeal) Y := hYtors.module
    letI : Module (A ⧸ I.asIdeal) Z := hZtors.module
    let YB : ModuleCat.{v} (A ⧸ I.asIdeal) := ModuleCat.of _ Y
    let ZB : ModuleCat.{v} (A ⧸ I.asIdeal) := ModuleCat.of _ Z
    let eA : (ModuleCat.restrictScalars q).obj M ≅
        ModuleCat.of A (Y × Z) :=
      e.trans (ModuleCat.biprodIsoProd Y Z)
    let lA : (ModuleCat.restrictScalars q).obj M ≃ₗ[A] (Y × Z) :=
      eA.toLinearEquiv
    let lB : M ≃ₗ[A ⧸ I.asIdeal] (Y × Z) :=
      { toFun := lA
        invFun := lA.symm
        left_inv := lA.left_inv
        right_inv := lA.right_inv
        map_add' := lA.map_add
        map_smul' := by
          intro b x
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
          change lA (a • (show
              (ModuleCat.restrictScalars q).obj M from x)) = q a • lA x
          have hp : q a • lA x = a • lA x := by
            apply Prod.ext
            · exact hYtors.mk_smul a (lA x).1
            · exact hZtors.mk_smul a (lA x).2
          rw [hp]
          exact lA.map_smul a x }
    let eBProd : M ≅ ModuleCat.of (A ⧸ I.asIdeal) (Y × Z) :=
      lB.toModuleIso
    let eB : M ≅ YB ⊞ ZB :=
      eBProd.trans (ModuleCat.biprodIsoProd YB ZB).symm
    rcases hM.2 YB ZB eB with hYB | hZB
    · left
      rw [ModuleCat.isZero_iff_subsingleton] at hYB ⊢
      exact hYB
    · right
      rw [ModuleCat.isZero_iff_subsingleton] at hZB ⊢
      exact hZB

/-- Representation-finiteness descends to every two-sided algebra
quotient. -/
theorem IsRepresentationFinite.quotient
    (hA : IsRepresentationFinite k A) (I : TwoSidedIdeal A) :
    IsRepresentationFinite k (A ⧸ I.asIdeal) := by
  obtain ⟨n, X, hX, hcover⟩ := hA
  let q := Ideal.Quotient.mk I.asIdeal
  let Occurs : Fin n → Prop := fun i ↦
    ∃ M : ModuleCat.{v} (A ⧸ I.asIdeal),
      IsFiniteIndecomposable k (A ⧸ I.asIdeal) M ∧
        Nonempty ((ModuleCat.restrictScalars q).obj M ≅ X i)
  let C := {i : Fin n // Occurs i}
  letI : Fintype C := Fintype.ofFinite C
  let E : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let Yc : C → ModuleCat.{v} (A ⧸ I.asIdeal) := fun i ↦
    Classical.choose i.property
  have hYc (i : C) :
      IsFiniteIndecomposable k (A ⧸ I.asIdeal) (Yc i) ∧
        Nonempty ((ModuleCat.restrictScalars q).obj (Yc i) ≅ X i.1) :=
    Classical.choose_spec i.property
  refine ⟨Fintype.card C, fun j ↦ Yc (E.symm j), ?_, ?_⟩
  · intro j
    exact (hYc (E.symm j)).1
  · intro M hM
    letI : Module.Finite k M := hM.1
    letI : Module.Finite k ((ModuleCat.restrictScalars q).obj M) :=
      Module.Finite.equiv (quotientRestrictLinearEquiv I M)
    have hMind : Indecomposable
        ((ModuleCat.restrictScalars q).obj M) :=
      quotientRestrict_indecomposable I M hM.2
    obtain ⟨i, ⟨eM⟩⟩ := hcover
      ((ModuleCat.restrictScalars q).obj M) ⟨inferInstance, hMind⟩
    let c : C := ⟨i, ⟨M, hM, ⟨eM⟩⟩⟩
    refine ⟨E c, ?_⟩
    change Nonempty (M ≅ Yc (E.symm (E c)))
    rw [E.symm_apply_apply]
    obtain ⟨eY⟩ := (hYc c).2
    exact ⟨quotientRestrictIso I (eM.trans eY.symm)⟩

end MagnitudeConjecture.LeftModule
