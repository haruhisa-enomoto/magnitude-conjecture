import MagnitudeConjecture.CategoryTheory.FiniteOrbitRadicalComponents
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableInjectiveBoundary

/-!
# The injective radical boundary under finite orbit push-down

The source-shifted radical Hom spaces assemble into the radical Hom space of
the shift-orbit category.  Finite direct-sum duality then identifies push-down
of `D rad(-,X)` with the corresponding downstairs dual radical quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uS

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- Transporting a dependent subtype element transports its underlying value
heterogeneously. -/
theorem subtype_transport_val_heq
    {I : Sort uS} {V : I → Sort v} {P : ∀ i, V i → Prop}
    {i j : I} (h : i = j) (x : Subtype (P i)) :
    x.1 ≍ (h ▸ x : Subtype (P j)).1 := by
  subst j
  rfl

/-- An additive equivalence preserves the categorical radical. -/
theorem isRadicalMorphism_map_equivalence
    {D : Type u} [Category.{v} D] [Preadditive D]
    (E : C ≌ D) [E.functor.Additive]
    {X Y : C} {f : X ⟶ Y} (hf : IsRadicalMorphism f) :
    IsRadicalMorphism (E.functor.map f) := by
  intro g
  let g₀ : Y ⟶ X := E.functor.preimage g
  haveI : IsIso (𝟙 X - f ≫ g₀) := hf g₀
  haveI : IsIso (E.functor.map (𝟙 X - f ≫ g₀)) :=
    E.functor.map_isIso (𝟙 X - f ≫ g₀)
  have heq : E.functor.map (𝟙 X - f ≫ g₀) =
      𝟙 (E.functor.obj X) - E.functor.map f ≫ g := by
    rw [E.functor.map_sub, E.functor.map_id, E.functor.map_comp,
      E.functor.map_preimage]
  rw [← heq]
  infer_instance

variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- Moving a source shift to the target preserves radical morphisms. -/
theorem shiftSourceHomLinearEquiv_isRadicalMorphism
    (Y X : C) (b : A)
    (g : radicalHomSubmodule k ((shiftFunctor C b).obj Y) X) :
    IsRadicalMorphism
      (shiftSourceHomLinearEquiv (k := k) Y X b (-b) rfl g.1) := by
  letI : (shiftEquiv C b).inverse.Additive :=
    (inferInstance : (shiftFunctor C (-b)).Additive)
  let E : C ≌ C := (shiftEquiv C b).symm
  letI : E.functor.Additive :=
    (inferInstance : (shiftFunctor C (-b)).Additive)
  have hmap : IsRadicalMorphism
      (E.functor.map g.1) :=
    isRadicalMorphism_map_equivalence E g.2
  rw [shiftSourceHomLinearEquiv_apply]
  exact isRadicalMorphism_precomp
    (a := (shiftEquiv C b).unit.app Y) hmap

/-- Variant of source-shift radical preservation with an explicit target
degree equal to the negative source degree. -/
theorem shiftSourceHomLinearEquiv_isRadicalMorphism_of_eq
    (Y X : C) (b a : A) (h : -b = a)
    (g : radicalHomSubmodule k ((shiftFunctor C b).obj Y) X) :
    IsRadicalMorphism
      (shiftSourceHomLinearEquiv (k := k) Y X b a h g.1) := by
  subst a
  exact shiftSourceHomLinearEquiv_isRadicalMorphism (k := k) Y X b g

/-- Moving a target shift back to the source preserves radical morphisms. -/
theorem shiftSourceHomLinearEquiv_symm_isRadicalMorphism
    (Y X : C) (b : A) (q : ShiftHom Y X (-b))
    (hq : IsRadicalMorphism q) :
    IsRadicalMorphism
      ((shiftSourceHomLinearEquiv (k := k) Y X b (-b) rfl).symm q) := by
  letI : (shiftEquiv C b).functor.Additive :=
    (inferInstance : (shiftFunctor C b).Additive)
  have hmap : IsRadicalMorphism ((shiftEquiv C b).functor.map q) :=
    isRadicalMorphism_map_equivalence (shiftEquiv C b) hq
  rw [shiftSourceHomLinearEquiv_symm_apply]
  exact isRadicalMorphism_postcomp
    (b := (shiftEquiv C b).counit.app X) hmap

set_option maxHeartbeats 800000 in
/-- The `b`-component of the inverse source-shift decomposition of a radical
orbit morphism, bundled with its radical-membership proof. -/
noncomputable def orbitRadicalShiftSourceComponent
    (hcomponents : ∀ (Y X : C) (q : ShiftOrbitHom A Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory C A from Y) ⟶
              (show ShiftOrbitCategory C A from X) from q) ↔
        ∀ a : A, IsRadicalMorphism (q a))
    (Y X : C)
    (q : radicalHomSubmodule k
      (show ShiftOrbitCategory C A from Y)
      (show ShiftOrbitCategory C A from X)) (b : A) :
    radicalHomSubmodule k ((shiftFunctor C b).obj Y) X := by
  let q' : ShiftOrbitHom A ((shiftFunctor C b).obj Y) X :=
    shiftOrbitCompHom (shiftOrbitFromShift Y b) q.1
  have hq' : IsRadicalMorphism
      (show (show ShiftOrbitCategory C A from
          (shiftFunctor C b).obj Y) ⟶
        (show ShiftOrbitCategory C A from X) from q') :=
    isRadicalMorphism_precomp (shiftOrbitFromShift Y b) q.2
  have hzeroShift : IsRadicalMorphism (q' (0 : A)) :=
    (hcomponents ((shiftFunctor C b).obj Y) X q').mp hq' (0 : A)
  have hzero : IsRadicalMorphism
      (shiftOrbitZeroComponentLinearMap
        (k := k) (A := A) ((shiftFunctor C b).obj Y) X q') := by
    change IsRadicalMorphism
      ((shiftHomZeroLinearEquiv (k := k) (A := A)
        ((shiftFunctor C b).obj Y) X).symm (q' (0 : A)))
    change IsRadicalMorphism
      (q' (0 : A) ≫ (shiftFunctorZero' C (0 : A) rfl).hom.app X)
    exact isRadicalMorphism_postcomp
      (b := (shiftFunctorZero' C (0 : A) rfl).hom.app X) hzeroShift
  exact ⟨DirectSum.component k A
      (fun c ↦ ((shiftFunctor C c).obj Y ⟶ X)) b
      ((shiftSourceHomDirectSumEquiv
        (k := k) (A := A) Y X).symm q.1), by
    rw [shiftSourceHomDirectSumEquiv_symm_apply_component]
    exact hzero⟩

/-- The source-shifted radical components of a radical orbit morphism. -/
noncomputable def orbitRadicalToShiftSourceRadicalDirectSumFun
    (hcomponents : ∀ (Y X : C) (q : ShiftOrbitHom A Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory C A from Y) ⟶
              (show ShiftOrbitCategory C A from X) from q) ↔
        ∀ a : A, IsRadicalMorphism (q a))
    (Y X : C)
    (q : radicalHomSubmodule k
      (show ShiftOrbitCategory C A from Y)
      (show ShiftOrbitCategory C A from X)) :
    DirectSum A
      (fun b ↦ radicalHomSubmodule k ((shiftFunctor C b).obj Y) X) := by
  classical
  let z := (shiftSourceHomDirectSumEquiv
    (k := k) (A := A) Y X).symm q.1
  exact DFinsupp.mk z.support fun b ↦
    orbitRadicalShiftSourceComponent
      (k := k) hcomponents Y X q b.1

@[simp]
theorem orbitRadicalToShiftSourceRadicalDirectSum_apply_val
    (hcomponents : ∀ (Y X : C) (q : ShiftOrbitHom A Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory C A from Y) ⟶
              (show ShiftOrbitCategory C A from X) from q) ↔
        ∀ a : A, IsRadicalMorphism (q a))
    (Y X : C)
    (q : radicalHomSubmodule k
      (show ShiftOrbitCategory C A from Y)
      (show ShiftOrbitCategory C A from X)) (b : A) :
    ((orbitRadicalToShiftSourceRadicalDirectSumFun
      (k := k) hcomponents Y X q) b).1 =
      ((shiftSourceHomDirectSumEquiv
        (k := k) (A := A) Y X).symm q.1) b := by
  classical
  let z := (shiftSourceHomDirectSumEquiv
    (k := k) (A := A) Y X).symm q.1
  by_cases hb : b ∈ z.support
  · simp [orbitRadicalToShiftSourceRadicalDirectSumFun, z, hb,
      orbitRadicalShiftSourceComponent]
    change z b = z b
    rfl
  · have hzero : z b = 0 := by
      simpa [DFinsupp.mem_support_toFun] using hb
    simp [orbitRadicalToShiftSourceRadicalDirectSumFun, z, hb, hzero]

/-- A radical orbit morphism decomposes linearly into source-shifted radical
components. -/
noncomputable def orbitRadicalToShiftSourceRadicalDirectSum
    (hcomponents : ∀ (Y X : C) (q : ShiftOrbitHom A Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory C A from Y) ⟶
              (show ShiftOrbitCategory C A from X) from q) ↔
        ∀ a : A, IsRadicalMorphism (q a))
    (Y X : C) :
    radicalHomSubmodule k
        (show ShiftOrbitCategory C A from Y)
        (show ShiftOrbitCategory C A from X) →ₗ[k]
      DirectSum A
        (fun b ↦ radicalHomSubmodule k ((shiftFunctor C b).obj Y) X) where
  toFun := orbitRadicalToShiftSourceRadicalDirectSumFun
    (k := k) hcomponents Y X
  map_add' q r := by
    apply DFinsupp.ext
    intro b
    apply Subtype.ext
    change
      ((orbitRadicalToShiftSourceRadicalDirectSumFun
        (k := k) hcomponents Y X (q + r)) b).1 =
      ((orbitRadicalToShiftSourceRadicalDirectSumFun
        (k := k) hcomponents Y X q) b).1 +
      ((orbitRadicalToShiftSourceRadicalDirectSumFun
        (k := k) hcomponents Y X r) b).1
    rw [orbitRadicalToShiftSourceRadicalDirectSum_apply_val,
      orbitRadicalToShiftSourceRadicalDirectSum_apply_val,
      orbitRadicalToShiftSourceRadicalDirectSum_apply_val]
    change ((shiftSourceHomDirectSumEquiv
      (k := k) (A := A) Y X).symm (q.1 + r.1)) b = _
    rw [map_add]
    rfl
  map_smul' a q := by
    apply DFinsupp.ext
    intro b
    apply Subtype.ext
    change
      ((orbitRadicalToShiftSourceRadicalDirectSumFun
        (k := k) hcomponents Y X (a • q)) b).1 =
      a • ((orbitRadicalToShiftSourceRadicalDirectSumFun
        (k := k) hcomponents Y X q) b).1
    rw [orbitRadicalToShiftSourceRadicalDirectSum_apply_val,
      orbitRadicalToShiftSourceRadicalDirectSum_apply_val]
    change ((shiftSourceHomDirectSumEquiv
      (k := k) (A := A) Y X).symm (a • q.1)) b = _
    rw [map_smul]
    rfl

/-- Source-shifted radical components assemble into a radical orbit
morphism. -/
noncomputable def shiftSourceRadicalDirectSumToOrbitRadical
    (hcomponents : ∀ (Y X : C) (q : ShiftOrbitHom A Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory C A from Y) ⟶
              (show ShiftOrbitCategory C A from X) from q) ↔
        ∀ a : A, IsRadicalMorphism (q a))
    (Y X : C) :
    DirectSum A
        (fun b ↦ radicalHomSubmodule k ((shiftFunctor C b).obj Y) X) →ₗ[k]
      radicalHomSubmodule k
        (show ShiftOrbitCategory C A from Y)
        (show ShiftOrbitCategory C A from X) where
  toFun z := ⟨shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X
      (DirectSum.lmap (fun b ↦
        (radicalHomSubmodule k ((shiftFunctor C b).obj Y) X).subtype) z), by
    classical
    induction z using DirectSum.induction_on with
    | zero =>
        simp only [map_zero]
        exact isRadicalMorphism_zero
    | of b g =>
        have hi : (Equiv.neg A).symm (-b) = b := by
          apply (Equiv.neg A).injective
          simp only [Equiv.neg_apply, Equiv.apply_symm_apply]
        let g' : radicalHomSubmodule k
            ((shiftFunctor C ((Equiv.neg A).symm (-b))).obj Y) X :=
          hi.symm ▸ g
        have hshift := shiftSourceHomLinearEquiv_isRadicalMorphism_of_eq
          (k := k) Y X ((Equiv.neg A).symm (-b)) (-b)
            (neg_negEquiv_symm (-b)) g'
        have hfull :
            shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X
                (DirectSum.lmap (fun b ↦
                  (radicalHomSubmodule k
                    ((shiftFunctor C b).obj Y) X).subtype)
                  (DirectSum.of
                    (fun b ↦ radicalHomSubmodule k
                      ((shiftFunctor C b).obj Y) X) b g)) =
              shiftOrbitLof (k := k) Y X (-b)
                (shiftSourceHomLinearEquiv (k := k) Y X
                  ((Equiv.neg A).symm (-b)) (-b)
                  (neg_negEquiv_symm (-b)) g'.1) := by
          rw [DirectSum.lmap_of]
          have hinclusion := shiftSourceHomDirectSumEquiv_inclusion_neg
            (k := k) Y X (-b) g'.1
          convert hinclusion using 1
          simp only [directSumInclusion, DirectSum.lof_eq_of]
          apply congrArg (shiftSourceHomDirectSumEquiv
            (k := k) (A := A) Y X)
          change (DFinsupp.single b g.1 : DirectSum A
              (fun c ↦ ((shiftFunctor C c).obj Y ⟶ X))) =
            DFinsupp.single ((Equiv.neg A).symm (-b)) g'.1
          apply (DFinsupp.single_eq_single_iff _ _ _ _).mpr
          have hg : g.1 ≍ g'.1 := by
            exact subtype_transport_val_heq
              (V := fun c ↦ ((shiftFunctor C c).obj Y ⟶ X))
              (P := fun _ f ↦ IsRadicalMorphism f) hi.symm g
          exact Or.inl ⟨hi.symm, hg⟩
        apply (hcomponents Y X _).mpr
        intro a
        rw [hfull]
        by_cases ha : -b = a
        · subst a
          simpa [shiftOrbitLof_apply, shiftOrbitOf] using hshift
        · simp [shiftOrbitLof_apply, shiftOrbitOf,
            DirectSum.of_apply, ha]
          exact isRadicalMorphism_zero
    | add z r hz hr =>
        change IsRadicalMorphism
          (show (show ShiftOrbitCategory C A from Y) ⟶
              (show ShiftOrbitCategory C A from X) from
          (shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X
              (DirectSum.lmap (fun b ↦
                (radicalHomSubmodule k
                  ((shiftFunctor C b).obj Y) X).subtype) (z + r))))
        simpa only [map_add] using isRadicalMorphism_add hz hr⟩
  map_add' z r := by
    apply Subtype.ext
    simp
  map_smul' a z := by
    apply Subtype.ext
    simp

/-- The categorical radical in the orbit category is exactly the direct sum
of the source-shifted upstairs radical spaces. -/
noncomputable def orbitRadicalShiftSourceDirectSumEquiv
    (hcomponents : ∀ (Y X : C) (q : ShiftOrbitHom A Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory C A from Y) ⟶
              (show ShiftOrbitCategory C A from X) from q) ↔
        ∀ a : A, IsRadicalMorphism (q a))
    (Y X : C) :
    radicalHomSubmodule k
        (show ShiftOrbitCategory C A from Y)
        (show ShiftOrbitCategory C A from X) ≃ₗ[k]
      DirectSum A
        (fun b ↦ radicalHomSubmodule k ((shiftFunctor C b).obj Y) X) where
  toLinearMap := orbitRadicalToShiftSourceRadicalDirectSum
    (k := k) hcomponents Y X
  invFun := shiftSourceRadicalDirectSumToOrbitRadical
    (k := k) hcomponents Y X
  left_inv q := by
    apply Subtype.ext
    change shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X
        (DirectSum.lmap (fun b ↦
          (radicalHomSubmodule k ((shiftFunctor C b).obj Y) X).subtype)
          (orbitRadicalToShiftSourceRadicalDirectSumFun
            (k := k) hcomponents Y X q)) = q.1
    apply (shiftSourceHomDirectSumEquiv
      (k := k) (A := A) Y X).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    apply DFinsupp.ext
    intro b
    rw [DirectSum.lmap_apply]
    exact orbitRadicalToShiftSourceRadicalDirectSum_apply_val
      (k := k) hcomponents Y X q b
  right_inv z := by
    apply DFinsupp.ext
    intro b
    apply Subtype.ext
    change
      ((orbitRadicalToShiftSourceRadicalDirectSumFun
        (k := k) hcomponents Y X
        ((shiftSourceRadicalDirectSumToOrbitRadical
          (k := k) hcomponents Y X) z)) b).1 = (z b).1
    rw [orbitRadicalToShiftSourceRadicalDirectSum_apply_val]
    change ((shiftSourceHomDirectSumEquiv
      (k := k) (A := A) Y X).symm
        (shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X
          (DirectSum.lmap (fun b ↦
            (radicalHomSubmodule k
              ((shiftFunctor C b).obj Y) X).subtype) z))) b = (z b).1
    rw [LinearEquiv.symm_apply_apply]
    rw [DirectSum.lmap_apply]
    rfl

section DualRadicalComparison

universe uR vR

variable {kR : Type vR} [Field kR]
variable {CR : Type uR} [Category.{vR} CR] [Preadditive CR]
variable [CategoryTheory.Linear kR CR]
variable {AR : Type vR} [AddGroup AR] [HasShift CR AR]
variable [∀ a : AR, (shiftFunctor CR a).Additive]
variable [∀ a : AR, (shiftFunctor CR a).Linear kR]

/-- The objectwise finite-duality comparison for the dual radical
corepresentable. -/
noncomputable def orbitPushdownDualRadicalLinearYonedaValueEquiv
    (X Y : CR)
    (hcomponents : ∀ (Y X : CR) (q : ShiftOrbitHom AR Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from Y) ⟶
              (show ShiftOrbitCategory CR AR from X) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a))
    (hY : {b : AR | Nontrivial
      (Module.Dual kR
        (radicalHomSubmodule kR ((shiftFunctor CR b).obj Y) X))}.Finite) :
    orbitPushdownValue (A := AR)
        (dualRadicalLinearYoneda (k := kR) X) Y ≃ₗ[kR]
      Module.Dual kR
        (radicalHomSubmodule kR
          (show ShiftOrbitCategory CR AR from Y)
          (show ShiftOrbitCategory CR AR from X)) :=
  directSumDualEquivDualOfFiniteDual (k := kR)
      (fun b ↦ radicalHomSubmodule kR ((shiftFunctor CR b).obj Y) X) hY ≪≫ₗ
    (orbitRadicalShiftSourceDirectSumEquiv
      (k := kR) hcomponents Y X).dualMap

@[simp]
theorem orbitPushdownDualRadicalLinearYonedaValueEquiv_apply
    (X Y : CR)
    (hcomponents : ∀ (Y X : CR) (q : ShiftOrbitHom AR Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from Y) ⟶
              (show ShiftOrbitCategory CR AR from X) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a))
    (hY : {b : AR | Nontrivial
      (Module.Dual kR
        (radicalHomSubmodule kR ((shiftFunctor CR b).obj Y) X))}.Finite)
    (Phi : orbitPushdownValue (A := AR)
      (dualRadicalLinearYoneda (k := kR) X) Y)
    (q : radicalHomSubmodule kR
      (show ShiftOrbitCategory CR AR from Y)
      (show ShiftOrbitCategory CR AR from X)) :
    orbitPushdownDualRadicalLinearYonedaValueEquiv
        (kR := kR) X Y hcomponents hY Phi q =
      directSumDualToDual (k := kR)
        (fun b ↦ radicalHomSubmodule kR ((shiftFunctor CR b).obj Y) X)
        Phi
        (orbitRadicalShiftSourceDirectSumEquiv
          (k := kR) hcomponents Y X q) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The dual-radical comparison is the restriction quotient of the full
dual-corepresentable comparison. -/
theorem orbitPushdownDualRadicalValueEquiv_projection_square
    (X Y : CR)
    (hcomponents : ∀ (Y X : CR) (q : ShiftOrbitHom AR Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from Y) ⟶
              (show ShiftOrbitCategory CR AR from X) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a))
    (hY : {b : AR | Nontrivial
      (Module.Dual kR
        (radicalHomSubmodule kR ((shiftFunctor CR b).obj Y) X))}.Finite) :
    ((dualLinearYonedaRadicalProjectionNatTrans (k := kR)
        (C := ShiftOrbitCategory CR AR)
        (show ShiftOrbitCategory CR AR from X)).app
      (show ShiftOrbitCategory CR AR from Y)).hom.comp
        (orbitPushdownDualLinearYonedaComparisonApp
          (k := kR) (A := AR) X Y) =
      (orbitPushdownDualRadicalLinearYonedaValueEquiv
        (kR := kR) X Y hcomponents hY).toLinearMap.comp
        (orbitPushdownNatTransAppLinear (A := AR)
          (dualLinearYonedaRadicalProjectionNatTrans (k := kR) X) Y) := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro q
  change Module.Dual kR (((shiftFunctor CR b).obj Y) ⟶ X) at phi
  change
    (show Module.Dual kR
        (radicalHomSubmodule kR
          (show ShiftOrbitCategory CR AR from Y)
          (show ShiftOrbitCategory CR AR from X)) from
      ((dualLinearYonedaRadicalProjectionNatTrans (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X)).app
        (show ShiftOrbitCategory CR AR from Y)
        (orbitPushdownDualLinearYonedaComparisonApp
          (k := kR) (A := AR) X Y
          (orbitPushdownLof (dualLinearYoneda (k := kR) X) Y b phi)))) q =
    orbitPushdownDualRadicalLinearYonedaValueEquiv
      (kR := kR) X Y hcomponents hY
      (orbitPushdownNatTransAppLinear (A := AR)
        (dualLinearYonedaRadicalProjectionNatTrans (k := kR) X) Y
        (orbitPushdownLof (dualLinearYoneda (k := kR) X) Y b phi)) q
  rw [orbitPushdownDualLinearYonedaComparisonApp_lof,
    orbitPushdownNatTransAppLinear_lof,
    orbitPushdownDualRadicalLinearYonedaValueEquiv_apply]
  change phi
      (shiftOrbitZeroComponentLinearMap
        (k := kR) (A := AR) ((shiftFunctor CR b).obj Y) X
        (shiftOrbitCompHom (shiftOrbitFromShift Y b) q.1)) =
    directSumDualToDual (k := kR)
      (fun c ↦ radicalHomSubmodule kR ((shiftFunctor CR c).obj Y) X)
      (directSumInclusion (k := kR)
        (fun c ↦ Module.Dual kR
          (radicalHomSubmodule kR ((shiftFunctor CR c).obj Y) X)) b
        ((radicalHomSubmodule kR
          ((shiftFunctor CR b).obj Y) X).subtype.dualMap phi))
      (orbitRadicalShiftSourceDirectSumEquiv
        (k := kR) hcomponents Y X q)
  rw [directSumDualToDual_lof_apply]
  change phi
      (shiftOrbitZeroComponentLinearMap
        (k := kR) (A := AR) ((shiftFunctor CR b).obj Y) X
        (shiftOrbitCompHom (shiftOrbitFromShift Y b) q.1)) =
    phi (((orbitRadicalToShiftSourceRadicalDirectSumFun
      (k := kR) hcomponents Y X q) b).1)
  rw [orbitRadicalToShiftSourceRadicalDirectSum_apply_val]
  change phi
      (shiftOrbitZeroComponentLinearMap
        (k := kR) (A := AR) ((shiftFunctor CR b).obj Y) X
        (shiftOrbitCompHom (shiftOrbitFromShift Y b) q.1)) =
    phi (DirectSum.component kR AR
      (fun c ↦ ((shiftFunctor CR c).obj Y ⟶ X)) b
      ((shiftSourceHomDirectSumEquiv
        (k := kR) (A := AR) Y X).symm q.1))
  rw [shiftSourceHomDirectSumEquiv_symm_apply_component]

/-- If all translated dual radical values have finite support, push-down of
`D rad(-,X)` is naturally the downstairs `D rad(-,X)`. -/
noncomputable def orbitPushdownDualRadicalLinearYonedaIso
    (X : CR)
    (hcomponents : ∀ (Y X : CR) (q : ShiftOrbitHom AR Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from Y) ⟶
              (show ShiftOrbitCategory CR AR from X) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a))
    (hX : ∀ Y : CR, {b : AR | Nontrivial
      (Module.Dual kR
        (radicalHomSubmodule kR ((shiftFunctor CR b).obj Y) X))}.Finite) :
    orbitPushdown (A := AR) (dualRadicalLinearYoneda (k := kR) X) ≅
      dualRadicalLinearYoneda (k := kR)
        (C := ShiftOrbitCategory CR AR)
        (show ShiftOrbitCategory CR AR from X) := by
  refine NatIso.ofComponents (fun Y ↦
    (orbitPushdownDualRadicalLinearYonedaValueEquiv
      (kR := kR) X (show CR from Y) hcomponents
        (hX (show CR from Y))).toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro psi
  let p := dualLinearYonedaRadicalProjectionNatTrans (k := kR) X
  let eY := orbitPushdownDualRadicalLinearYonedaValueEquiv
    (kR := kR) X (show CR from Y) hcomponents (hX (show CR from Y))
  let eZ := orbitPushdownDualRadicalLinearYonedaValueEquiv
    (kR := kR) X (show CR from Z) hcomponents (hX (show CR from Z))
  have hp : Function.Surjective
      (orbitPushdownNatTransAppLinear (A := AR) p (show CR from Y)) := by
    apply orbitPushdownNatTransAppLinear_surjective
    intro W
    exact LinearMap.dualMap_surjective_of_injective
      (radicalHomSubmodule kR W X).subtype_injective
  obtain ⟨phi, rfl⟩ := hp psi
  have hfull := (orbitPushdownDualLinearYonedaComparison
    (k := kR) (A := AR) X).naturality f
  have hpNat := (orbitPushdownNatTrans (A := AR) p).naturality f
  have hdownNat := (dualLinearYonedaRadicalProjectionNatTrans
    (k := kR) (C := ShiftOrbitCategory CR AR)
    (show ShiftOrbitCategory CR AR from X)).naturality f
  have hsqY := orbitPushdownDualRadicalValueEquiv_projection_square
    (kR := kR) X (show CR from Y) hcomponents (hX (show CR from Y))
  have hsqZ := orbitPushdownDualRadicalValueEquiv_projection_square
    (kR := kR) X (show CR from Z) hcomponents (hX (show CR from Z))
  change eZ
      (orbitPushdownMapLinear (dualRadicalLinearYoneda (k := kR) X) f
        (orbitPushdownNatTransAppLinear (A := AR) p
          (show CR from Y) phi)) =
    (dualRadicalLinearYoneda (k := kR)
      (C := ShiftOrbitCategory CR AR)
      (show ShiftOrbitCategory CR AR from X)).map f
        (eY (orbitPushdownNatTransAppLinear (A := AR) p
          (show CR from Y) phi))
  calc
    eZ (orbitPushdownMapLinear (dualRadicalLinearYoneda (k := kR) X) f
        (orbitPushdownNatTransAppLinear (A := AR) p
          (show CR from Y) phi)) =
      eZ (orbitPushdownNatTransAppLinear (A := AR) p
        (show CR from Z)
        (orbitPushdownMapLinear (dualLinearYoneda (k := kR) X) f phi)) := by
          exact congrArg eZ
            (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hpNat) phi).symm
    _ = (dualLinearYonedaRadicalProjectionNatTrans (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X)).app Z
        (orbitPushdownDualLinearYonedaComparisonApp
          (k := kR) (A := AR) X (show CR from Z)
          (orbitPushdownMapLinear (dualLinearYoneda (k := kR) X) f phi)) := by
          exact (LinearMap.congr_fun hsqZ
            (orbitPushdownMapLinear
              (dualLinearYoneda (k := kR) X) f phi)).symm
    _ = (dualLinearYonedaRadicalProjectionNatTrans (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X)).app Z
        ((dualLinearYoneda (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X)).map f
          (orbitPushdownDualLinearYonedaComparisonApp
            (k := kR) (A := AR) X (show CR from Y) phi)) := by
          exact congrArg
            (fun z ↦ (dualLinearYonedaRadicalProjectionNatTrans (k := kR)
              (C := ShiftOrbitCategory CR AR)
              (show ShiftOrbitCategory CR AR from X)).app Z z)
            (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hfull) phi)
    _ = (dualRadicalLinearYoneda (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X)).map f
        ((dualLinearYonedaRadicalProjectionNatTrans (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X)).app Y
          (orbitPushdownDualLinearYonedaComparisonApp
            (k := kR) (A := AR) X (show CR from Y) phi)) := by
          exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdownNat)
            (orbitPushdownDualLinearYonedaComparisonApp
              (k := kR) (A := AR) X (show CR from Y) phi)
    _ = (dualRadicalLinearYoneda (k := kR)
          (C := ShiftOrbitCategory CR AR)
          (show ShiftOrbitCategory CR AR from X)).map f
        (eY (orbitPushdownNatTransAppLinear (A := AR) p
          (show CR from Y) phi)) := by
          exact congrArg
            (fun z ↦ (dualRadicalLinearYoneda (k := kR)
              (C := ShiftOrbitCategory CR AR)
              (show ShiftOrbitCategory CR AR from X)).map f z)
            (LinearMap.congr_fun hsqY phi)

/-- The finite dual-radical isomorphism carries the pushed radical
restriction quotient to the literal downstairs quotient. -/
theorem orbitPushdownDualRadicalLinearYonedaIso_projection_square
    (X : CR)
    (hcomponents : ∀ (Y X : CR) (q : ShiftOrbitHom AR Y X),
      IsRadicalMorphism
          (show (show ShiftOrbitCategory CR AR from Y) ⟶
              (show ShiftOrbitCategory CR AR from X) from q) ↔
        ∀ a : AR, IsRadicalMorphism (q a))
    (hX : ∀ Y : CR, {b : AR | Nontrivial
      (Module.Dual kR
        (radicalHomSubmodule kR ((shiftFunctor CR b).obj Y) X))}.Finite)
    (hHom : ∀ Y : CR, {b : AR | Nontrivial
      (Module.Dual kR (((shiftFunctor CR b).obj Y ⟶ X)))}.Finite) :
    (orbitPushdownDualLinearYonedaIso
        (k := kR) (A := AR) X hHom).hom ≫
      dualLinearYonedaRadicalProjectionNatTrans (k := kR)
        (C := ShiftOrbitCategory CR AR)
        (show ShiftOrbitCategory CR AR from X) =
    orbitPushdownNatTrans (A := AR)
        (dualLinearYonedaRadicalProjectionNatTrans (k := kR) X) ≫
      (orbitPushdownDualRadicalLinearYonedaIso
        (kR := kR) X hcomponents hX).hom := by
  rw [orbitPushdownDualLinearYonedaIso_hom_eq_comparison]
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  change ((dualLinearYonedaRadicalProjectionNatTrans (k := kR)
      (C := ShiftOrbitCategory CR AR)
      (show ShiftOrbitCategory CR AR from X)).app
        (show ShiftOrbitCategory CR AR from Y)).hom.comp
      (orbitPushdownDualLinearYonedaComparisonApp
        (k := kR) (A := AR) X (show CR from Y)) =
    (orbitPushdownDualRadicalLinearYonedaValueEquiv
      (kR := kR) X (show CR from Y) hcomponents
        (hX (show CR from Y))).toLinearMap.comp
      (orbitPushdownNatTransAppLinear (A := AR)
        (dualLinearYonedaRadicalProjectionNatTrans (k := kR) X)
        (show CR from Y))
  exact orbitPushdownDualRadicalValueEquiv_projection_square
    (kR := kR) X (show CR from Y) hcomponents (hX (show CR from Y))

/-- Right composition with the inverse of an isomorphism on radical Hom
spaces. -/
def radicalRightCompInvLinearEquiv
    (Y : CR) {X X' : CR} (e : X ≅ X') :
    radicalHomSubmodule kR Y X' ≃ₗ[kR]
      radicalHomSubmodule kR Y X where
  toFun q := ⟨q.1 ≫ e.inv, isRadicalMorphism_postcomp e.inv q.2⟩
  invFun q := ⟨q.1 ≫ e.hom, isRadicalMorphism_postcomp e.hom q.2⟩
  left_inv q := by apply Subtype.ext; simp [Category.assoc]
  right_inv q := by apply Subtype.ext; simp [Category.assoc]
  map_add' q r := by apply Subtype.ext; simp
  map_smul' a q := by apply Subtype.ext; simp

/-- Dual radical corepresentables are invariant under changing their
representing object by an isomorphism. -/
noncomputable def dualRadicalLinearYonedaMapIso
    {X X' : CR} (e : X ≅ X') :
    dualRadicalLinearYoneda (k := kR) X ≅
      dualRadicalLinearYoneda (k := kR) X' := by
  refine NatIso.ofComponents (fun Y ↦
    (radicalRightCompInvLinearEquiv
      (kR := kR) (show CR from Y) e).dualMap.toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change Module.Dual kR (radicalHomSubmodule kR (show CR from Y) X) at phi
  apply LinearMap.ext
  intro q
  change phi ⟨f ≫ (q.1 ≫ e.inv), _⟩ =
    phi ⟨(f ≫ q.1) ≫ e.inv, _⟩
  congr 1
  apply Subtype.ext
  exact (Category.assoc f q.1 e.inv).symm

/-- Changing the representing object commutes with restriction from the full
dual corepresentable to its dual radical quotient. -/
theorem dualRadicalLinearYonedaMapIso_projection_square
    {X X' : CR} (e : X ≅ X') :
    (dualLinearYonedaMapIso (k := kR) e).hom ≫
        dualLinearYonedaRadicalProjectionNatTrans (k := kR) X' =
      dualLinearYonedaRadicalProjectionNatTrans (k := kR) X ≫
        (dualRadicalLinearYonedaMapIso (kR := kR) e).hom := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro q
  rfl

end DualRadicalComparison

namespace CoherentDeckShift

universe u' v'

variable {k' : Type v'} [Field k']
variable {C' : Type u'} [Category.{v'} C'] [Preadditive C']
variable {G : Type v'} [Group G] [MulAction G C'] [IsCancelSMul G C']
variable [CategoryTheory.Linear k' C']
variable (D : CoherentDeckShift C' G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k']

/-- Deck-specialized push-down preservation of the dual radical
corepresentable. -/
noncomputable def orbitPushdownDualRadicalLinearYonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    orbitPushdown (A := Additive G)
        (dualRadicalLinearYoneda (k := k') X) ≅
      dualRadicalLinearYoneda (k := k')
        (C := ShiftOrbitCategory C' (Additive G))
        (show ShiftOrbitCategory C' (Additive G) from X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let R := finiteDimensionalDualRadicalLinearYoneda (k := k') X hX
  exact MagnitudeConjecture.CoveringHom.orbitPushdownDualRadicalLinearYonedaIso
    (kR := k') X
      (fun Y Z ↦ D.shiftOrbitHom_isRadicalMorphism_iff_components
        (k' := k') hP hlocal hfree Y Z)
      (fun Y ↦ D.finite_nontrivial_shift_values (k := k') R Y)

/-- The deck-specialized dual-radical comparison identifies pushed radical
restriction with literal radical restriction in the shift-orbit category. -/
theorem orbitPushdownDualRadicalLinearYonedaIso_projection_square
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.orbitPushdownDualLinearYonedaIso (k := k') X hX).hom ≫
        dualLinearYonedaRadicalProjectionNatTrans (k := k')
          (C := ShiftOrbitCategory C' (Additive G))
          (show ShiftOrbitCategory C' (Additive G) from X) =
      orbitPushdownNatTrans (A := Additive G)
          (dualLinearYonedaRadicalProjectionNatTrans (k := k') X) ≫
        (D.orbitPushdownDualRadicalLinearYonedaIso
          (k' := k') hP hlocal hfree X hX).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let M := finiteDimensionalDualLinearYoneda (k := k') X hX
  let R := finiteDimensionalDualRadicalLinearYoneda (k := k') X hX
  exact
    MagnitudeConjecture.CoveringHom.orbitPushdownDualRadicalLinearYonedaIso_projection_square
    (kR := k') X
      (fun Y Z ↦ D.shiftOrbitHom_isRadicalMorphism_iff_components
        (k' := k') hP hlocal hfree Y Z)
      (fun Y ↦ D.finite_nontrivial_shift_values (k := k') R Y)
      (fun Y ↦ D.finite_nontrivial_shift_values (k := k') M Y)

/-- Restricting a dual radical corepresentable to chosen orbit
representatives gives the literal dual radical corepresentable on the orbit
skeleton. -/
noncomputable def deckOrbitRepresentativeDualRadicalLinearYonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (q : MulAction.orbitRel.Quotient G C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    deckOrbitRepresentativeFunctor (C := C') (G := G) ⋙
        dualRadicalLinearYoneda (k := k')
          (C := ShiftOrbitCategory C' (Additive G))
          (show ShiftOrbitCategory C' (Additive G) from
            deckOrbitRepresentative (C := C') (G := G) q) ≅
      dualRadicalLinearYoneda (k := k')
        (C := DeckOrbitSkeleton C' G) q := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  refine NatIso.ofComponents (fun Y ↦
    (D.deckOrbitRepresentativeRadicalHomLinearEquiv
      (k' := k') hP hlocal hfree Y q).symm.dualMap.toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro r
  rfl

/-- The chosen-representative dual-radical comparison commutes with radical
restriction. -/
theorem deckOrbitRepresentativeDualRadicalLinearYonedaIso_projection_square
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (q : MulAction.orbitRel.Quotient G C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.deckOrbitRepresentativeDualLinearYonedaIso (k := k') q).hom ≫
        dualLinearYonedaRadicalProjectionNatTrans (k := k')
          (C := DeckOrbitSkeleton C' G) q =
      Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C') (G := G))
          (dualLinearYonedaRadicalProjectionNatTrans (k := k')
            (C := ShiftOrbitCategory C' (Additive G))
            (show ShiftOrbitCategory C' (Additive G) from
              deckOrbitRepresentative (C := C') (G := G) q)) ≫
        (D.deckOrbitRepresentativeDualRadicalLinearYonedaIso
          (k' := k') hP hlocal hfree q).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro r
  rfl

/-- Skeletal Gabriel push-down preserves the dual radical corepresentable at
the strict orbit of `X`. -/
noncomputable def orbitSkeletonPushdownDualRadicalLinearYonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    orbitSkeletonPushdown (G := G)
        (dualRadicalLinearYoneda (k := k') X) ≅
      dualRadicalLinearYoneda (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := deckOrbitRepresentativeFunctor (C := C') (G := G)
  let Q : DeckOrbitSkeleton C' G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  exact Functor.isoWhiskerLeft J
      (D.orbitPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX) ≪≫
    Functor.isoWhiskerLeft J
      (dualRadicalLinearYonedaMapIso (kR := k')
        (D.objectIsoDeckOrbitRepresentative X)) ≪≫
    D.deckOrbitRepresentativeDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree Q

/-- Skeletal push-down carries radical restriction on a finite dual
corepresentable to literal radical restriction downstairs. -/
theorem orbitSkeletonPushdownDualRadicalLinearYonedaIso_projection_square
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.orbitSkeletonPushdownDualLinearYonedaIso
        (k := k') X hX).hom ≫
      dualLinearYonedaRadicalProjectionNatTrans (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') =
    Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C') (G := G))
        (orbitPushdownNatTrans (A := Additive G)
          (dualLinearYonedaRadicalProjectionNatTrans (k := k') X)) ≫
      (D.orbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := deckOrbitRepresentativeFunctor (C := C') (G := G)
  let Q : DeckOrbitSkeleton C' G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  let a₀ := Functor.whiskerLeft J
    (D.orbitPushdownDualLinearYonedaIso (k := k') X hX).hom
  let b₀ := Functor.whiskerLeft J
    (dualLinearYonedaMapIso (k := k')
      (D.objectIsoDeckOrbitRepresentative X)).hom
  let c₀ := (D.deckOrbitRepresentativeDualLinearYonedaIso
    (k := k') Q).hom
  let a := Functor.whiskerLeft J
    (D.orbitPushdownDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree X hX).hom
  let b := Functor.whiskerLeft J
    (dualRadicalLinearYonedaMapIso (kR := k')
      (D.objectIsoDeckOrbitRepresentative X)).hom
  let c := (D.deckOrbitRepresentativeDualRadicalLinearYonedaIso
    (k' := k') hP hlocal hfree Q).hom
  let p := Functor.whiskerLeft J
    (orbitPushdownNatTrans (A := Additive G)
      (dualLinearYonedaRadicalProjectionNatTrans (k := k') X))
  let iX := Functor.whiskerLeft J
    (dualLinearYonedaRadicalProjectionNatTrans (k := k')
      (C := ShiftOrbitCategory C' (Additive G))
      (show ShiftOrbitCategory C' (Additive G) from X))
  let iR := Functor.whiskerLeft J
    (dualLinearYonedaRadicalProjectionNatTrans (k := k')
      (C := ShiftOrbitCategory C' (Additive G))
      (show ShiftOrbitCategory C' (Additive G) from
        deckOrbitRepresentative (C := C') (G := G) Q))
  let iQ := dualLinearYonedaRadicalProjectionNatTrans (k := k')
    (C := DeckOrbitSkeleton C' G) Q
  change (a₀ ≫ b₀ ≫ c₀) ≫ iQ = p ≫ (a ≫ b ≫ c)
  have h₁ : a₀ ≫ iX = p ≫ a := by
    dsimp only [a₀, iX, p, a, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (D.orbitPushdownDualRadicalLinearYonedaIso_projection_square
        (k' := k') hP hlocal hfree X hX)
  have h₂ : b₀ ≫ iR = iX ≫ b := by
    dsimp only [b₀, iR, iX, b, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (dualRadicalLinearYonedaMapIso_projection_square
        (kR := k') (D.objectIsoDeckOrbitRepresentative X))
  have h₃ : c₀ ≫ iQ = iR ≫ c := by
    exact D.deckOrbitRepresentativeDualRadicalLinearYonedaIso_projection_square
      (k' := k') hP hlocal hfree Q
  calc
    (a₀ ≫ b₀ ≫ c₀) ≫ iQ = a₀ ≫ b₀ ≫ (c₀ ≫ iQ) := by
      simp only [Category.assoc]
    _ = a₀ ≫ b₀ ≫ (iR ≫ c) := by rw [h₃]
    _ = a₀ ≫ (b₀ ≫ iR) ≫ c := by simp only [Category.assoc]
    _ = a₀ ≫ (iX ≫ b) ≫ c := by rw [h₂]
    _ = (a₀ ≫ iX) ≫ b ≫ c := by simp only [Category.assoc]
    _ = (p ≫ a) ≫ b ≫ c := by rw [h₁]
    _ = p ≫ (a ≫ b ≫ c) := by simp only [Category.assoc]

/-- Bundled linear-module form of skeletal push-down preserving the dual
radical corepresentable. -/
noncomputable def linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (linearModuleOrbitSkeletonPushdown
        (k := k') (C := C') (G := G)).obj
        (dualRadicalLinearYonedaLinearModule (k := k') X) ≅
      dualRadicalLinearYonedaLinearModule (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  exact (IsLinearModule (C := DeckOrbitSkeleton C' G) k').ι.preimageIso
    (D.orbitSkeletonPushdownDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree X hX)

@[simp]
theorem linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso_hom_hom
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree X hX).hom.hom =
      (D.orbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := (IsLinearModule (C := DeckOrbitSkeleton C' G) k').ι
  let LX := (linearModuleOrbitSkeletonPushdown
    (k := k') (C := C') (G := G)).obj
      (dualRadicalLinearYonedaLinearModule (k := k') X)
  let RX := dualRadicalLinearYonedaLinearModule (k := k')
    (C := DeckOrbitSkeleton C' G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  change (J.preimage (X := LX) (Y := RX)
      (D.orbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom).hom = _
  exact J.map_preimage (X := LX) (Y := RX)
    (D.orbitSkeletonPushdownDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree X hX).hom

/-- The finite downstairs dual radical quotient associated to the strict
orbit of `X`. -/
noncomputable def orbitSkeletonFiniteDimensionalDualRadicalLinearYoneda
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C' G) k' := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  exact finiteDimensionalDualRadicalLinearYoneda (k := k')
    (C := DeckOrbitSkeleton C' G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
    (D.orbitSkeletonFiniteDimensionalDualLinearYoneda (k := k') X hX).property

/-- Finite-dimensional skeletal push-down preserves the dual radical
quotient. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).obj
        (finiteDimensionalDualRadicalLinearYoneda (k := k') X hX) ≅
      D.orbitSkeletonFiniteDimensionalDualRadicalLinearYoneda
        (k' := k') X hX := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  exact (IsFiniteDimensionalModule
    (C := DeckOrbitSkeleton C' G) k').ι.preimageIso
      (D.linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX)

@[simp]
theorem finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso_hom_hom
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    (D.finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree X hX).hom.hom =
      (D.linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let J := (IsFiniteDimensionalModule
    (C := DeckOrbitSkeleton C' G) k').ι
  let LX := (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).obj
    (finiteDimensionalDualRadicalLinearYoneda (k := k') X hX)
  let RX := D.orbitSkeletonFiniteDimensionalDualRadicalLinearYoneda
    (k' := k') X hX
  change (J.preimage (X := LX) (Y := RX)
      (D.linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom).hom = _
  exact J.map_preimage (X := LX) (Y := RX)
    (D.linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree X hX).hom

/-- Finite-dimensional push-down carries the canonical injective radical
quotient to the canonical quotient at the strict orbit. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalProjection
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C')
    (hX : IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    let hX' :=
      (D.orbitSkeletonFiniteDimensionalDualLinearYoneda (k := k') X hX).property
    (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k') X hX).hom ≫
      finiteDimensionalDualLinearYonedaRadicalProjection (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') hX' =
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).map
        (finiteDimensionalDualLinearYonedaRadicalProjection
          (k := k') X hX) ≫
      (D.finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  let hX' :=
    (D.orbitSkeletonFiniteDimensionalDualLinearYoneda (k := k') X hX).property
  apply ObjectProperty.hom_ext
  change
    (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k') X hX).hom.hom ≫
      (finiteDimensionalDualLinearYonedaRadicalProjection (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C') hX').hom =
    ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).map
      (finiteDimensionalDualLinearYonedaRadicalProjection
        (k := k') X hX)).hom ≫
      (D.finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom.hom
  rw [finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom,
    finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso_hom_hom]
  apply ObjectProperty.hom_ext
  change
    (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k') X hX).hom.hom ≫
      (dualLinearYonedaRadicalProjection (k := k')
        (C := DeckOrbitSkeleton C' G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')).hom =
    ((linearModuleOrbitSkeletonPushdown
      (k := k') (C := C') (G := G)).map
      (dualLinearYonedaRadicalProjection (k := k') X)).hom ≫
      (D.linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
        (k' := k') hP hlocal hfree X hX).hom.hom
  rw [linearModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom,
    linearModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso_hom_hom]
  exact D.orbitSkeletonPushdownDualRadicalLinearYonedaIso_projection_square
    (k' := k') hP hlocal hfree X hX

set_option linter.unusedVariables false in
/-- The canonical left almost-split map out of an upstairs indecomposable
injective remains left almost split after finite-dimensional skeletal
push-down. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_dualRadicalProjection_isLeftAlmostSplit
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hI : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    letI := isLinearModule_stableUnderShift (k := k') D.core
    letI := linearModuleCategoryHasShift (k := k') D.core
    letI := linearModuleCategoryAdditiveShift (R := k') D.core
    letI := linearModuleCategoryLinearShift (R := k') D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k')
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k')
    letI := trivialHasShift
      (LinearModuleCategory.{u', v', v', v'}
        (C := ShiftOrbitCategory C' (Additive G)) k') (Additive G)
    IsLeftAlmostSplit
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).map
        (finiteDimensionalDualLinearYonedaRadicalProjection
          (k := k') X (hI X))) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  letI := isLinearModule_stableUnderShift (k := k') D.core
  letI := linearModuleCategoryHasShift (k := k') D.core
  letI := linearModuleCategoryAdditiveShift (R := k') D.core
  letI := linearModuleCategoryLinearShift (R := k') D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k')
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k')
  letI := trivialHasShift
    (LinearModuleCategory.{u', v', v', v'}
      (C := ShiftOrbitCategory C' (Additive G)) k') (Additive G)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')
  let I := finiteDimensionalDualLinearYoneda (k := k') X (hI X)
  let R := finiteDimensionalDualRadicalLinearYoneda
    (k := k') X (hI X)
  let m : I ⟶ R :=
    finiteDimensionalDualLinearYonedaRadicalProjection
      (k := k') X (hI X)
  let hI' := D.orbitSkeletonDualLinearYonedaFinite (k := k') hI
  let hlocal' : ∀ Q : DeckOrbitSkeleton C' G, IsLocalRing (End Q) :=
    D.orbitSkeleton_end_isLocalRing (k := k') hP hlocal hfree
  let Q : DeckOrbitSkeleton C' G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C')
  let mQ := finiteDimensionalDualLinearYonedaRadicalProjection
    (k := k') (C := DeckOrbitSkeleton C' G) Q (hI' Q)
  let eI := D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
    (k := k') X (hI X)
  let eR :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalLinearYonedaIso
      (k' := k') hP hlocal hfree X (hI X)
  have hmQ : IsLeftAlmostSplit mQ :=
    finiteDimensionalDualLinearYonedaRadicalProjection_isLeftAlmostSplit
      hI' hlocal' Q
  have hsource : IsLeftAlmostSplit (eI.hom ≫ mQ) :=
    hmQ.precomp_iso eI
  have hsquare : eI.hom ≫ mQ = P.map m ≫ eR.hom := by
    exact D.finiteDimensionalModuleOrbitSkeletonPushdownDualRadicalProjection
      (k' := k') hP hlocal hfree X (hI X)
  have hcomp : IsLeftAlmostSplit (P.map m ≫ eR.hom) := by
    rw [← hsquare]
    exact hsource
  have hback := hcomp.postcomp_iso eR.symm
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using hback

set_option linter.unusedVariables false in
/-- Injective boundary adjacency: every indecomposable admitting an
irreducible map from the push-down of an upstairs finite dual
corepresentable is itself the push-down of an upstairs indecomposable. -/
theorem exists_pushedIndecomposable_of_irreducible_from_injectivePushdown
    [IsMulTorsionFree G]
    (hP : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (linearCoyonedaLinearModule (k := k') X))
    (hI : ∀ X : C', IsFiniteDimensionalModule (C := C') k'
      (dualLinearYonedaLinearModule (k := k') X))
    (hlocal : ∀ X : C', IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C') (G := G))
    (X : C') :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k')
    letI := isLinearModule_stableUnderShift (k := k') D.core
    letI := linearModuleCategoryHasShift (k := k') D.core
    letI := linearModuleCategoryAdditiveShift (R := k') D.core
    letI := linearModuleCategoryLinearShift (R := k') D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k')
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k')
    letI := trivialHasShift
      (LinearModuleCategory.{u', v', v', v'}
        (C := ShiftOrbitCategory C' (Additive G)) k') (Additive G)
    ∀ {Y : FiniteDimensionalModuleCategory.{u', v', v', v'}
        (C := DeckOrbitSkeleton C' G) k'}
      (hY : Indecomposable Y)
      (f : (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')).obj
          (finiteDimensionalDualLinearYoneda (k := k') X (hI X)) ⟶ Y)
      (hf : IsIrreducibleMorphism f),
        ∃ Z : FiniteDimensionalModuleCategory.{u', v', v', v'}
            (C := C') k',
          Indecomposable Z ∧
            Nonempty
              ((D.finiteDimensionalModuleOrbitSkeletonPushdown
                (k := k')).obj Z ≅ Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k')
  letI := isLinearModule_stableUnderShift (k := k') D.core
  letI := linearModuleCategoryHasShift (k := k') D.core
  letI := linearModuleCategoryAdditiveShift (R := k') D.core
  letI := linearModuleCategoryLinearShift (R := k') D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k')
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k')
  letI := trivialHasShift
    (LinearModuleCategory.{u', v', v', v'}
      (C := ShiftOrbitCategory C' (Additive G)) k') (Additive G)
  intro Y hY f hf
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k')
  let I := finiteDimensionalDualLinearYoneda (k := k') X (hI X)
  let R := finiteDimensionalDualRadicalLinearYoneda
    (k := k') X (hI X)
  let m : I ⟶ R :=
    finiteDimensionalDualLinearYonedaRadicalProjection
      (k := k') X (hI X)
  have hPm : IsLeftAlmostSplit (P.map m) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_dualRadicalProjection_isLeftAlmostSplit
      (k' := k') hP hI hlocal hfree X
  apply
    MagnitudeConjecture.CategoryTheory.exists_essentialImage_of_irreducible_from_of_map_leftAlmostSplit
      P finiteDimensionalModule_finiteIndecomposableDecomposition
      (fun Z hZ ↦ ?_) m hPm hY
      (finiteDimensionalModule_end_isLocalRing k' Y hY) f hf
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k') Z hZ
        (D.finiteDimensionalModule_trivialStabilizer (k := k') Z hZ.1)

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
