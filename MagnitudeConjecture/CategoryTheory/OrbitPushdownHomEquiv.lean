import MagnitudeConjecture.CategoryTheory.OrbitPushdownFiniteSupport
import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso

/-!
# The Gabriel Hom equivalence for orbit push-down

This file proves the inverse identities between finite-support homogeneous
upstairs maps and transformations between their Gabriel push-down modules.
The first step computes degree extraction on a single homogeneous map.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A]
variable (D : ShiftMkCore C A)
variable [∀ a : A, (D.F a).Additive]
variable [∀ a : A, (D.F a).Linear k]

variable {I : Type w}

omit [Preadditive C] [CategoryTheory.Linear k C] in
/-- Mapping an equality arrow and then transporting back along the same
index equality is the identity on elements. -/
theorem moduleMap_eqToHom_cast
    (P : CategoryTheory.Functor C (ModuleCat.{uM} k)) (T : I → C)
    {b c : I} (h : b = c) (x : P.obj (T c)) :
    h ▸
        (P.map (eqToHom (congrArg T h.symm)) x) =
      x := by
  subst c
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Extracting degree `a` after descending a homogeneous degree-`a` map
recovers its value at every object and element. -/
theorem linearModuleOrbitPushdownDegreeValue_map
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (f : ShiftHom M₀ N₀ a) (X : C) (x : M₀.obj.obj X),
      (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv.app X
        (DirectSum.component k A
          (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (-a)
          (shiftedOrbitPushdownValueEquiv D N₀ a X
            (orbitPushdownNatTransAppLinear (A := A) f.hom X
              (orbitPushdownLof M₀.obj X 0
                (M₀.obj.map
                  ((shiftFunctorZero C A).inv.app X) x))))) =
        f.hom.app X x := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  intro f X x
  rw [orbitPushdownNatTransAppLinear_lof]
  change
    (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv.app X
      (DirectSum.component k A
        (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (-a)
        (shiftedOrbitPushdownValueEquiv D N₀ a X
          (orbitPushdownLof
            ((IsLinearModule (C := C) k).ι.obj (N₀⟦a⟧)) X 0
            (f.hom.app ((D.F 0).obj X)
              (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))))) = _
  rw [shiftedOrbitPushdownValueEquiv_lof]
  simp only [orbitPushdownLof]
  change
    (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv.app X
      (DirectSum.component k A
        (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (-a)
        (DirectSum.lof k A
          (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (0 + -a)
          (shiftedOrbitSummandEquiv D N₀ a 0 X
            (f.hom.app ((D.F 0).obj X)
              (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))))) = _
  rw [DirectSum.component.of]
  simp only [dif_pos (zero_add (-a))]
  let U := linearModuleShiftUnderlyingIso (k := k) D N₀ a
  let e : 0 + -a = -a := zero_add (-a)
  let castZeroAdd :
      N₀.obj.obj ((D.F (0 + -a)).obj X) →
        N₀.obj.obj ((D.F (-a)).obj X) :=
    fun y ↦ e ▸ y
  change U.inv.app X
      (castZeroAdd
        (N₀.obj.map ((D.add 0 (-a)).inv.app X)
          (U.hom.app ((D.F 0).obj X)
            (f.hom.app ((D.F 0).obj X)
              (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))))) = _
  let z := D.zero.inv.app X
  have hcat :
    M₀.obj.map z ≫ f.hom.app ((D.F 0).obj X) ≫
          U.hom.app ((D.F 0).obj X) ≫
            N₀.obj.map ((D.add 0 (-a)).inv.app X) =
        f.hom.app ((Functor.id C).obj X) ≫
          U.hom.app ((Functor.id C).obj X) ≫
          (D.F (-a) ⋙ N₀.obj).map z ≫
            N₀.obj.map ((D.add 0 (-a)).inv.app X) := by
    rw [f.hom.naturality_assoc]
    have hUcat := U.hom.naturality_assoc z
      (N₀.obj.map ((D.add 0 (-a)).inv.app X))
    exact congrArg
      (fun q ↦ f.hom.app ((Functor.id C).obj X) ≫ q) hUcat
  let h₀ : (D.F (-a)).obj ((Functor.id C).obj X) =
      (D.F (0 + -a)).obj X := by
    dsimp
    rw [zero_add]
  have hzero :
      (D.F (-a)).map z ≫ (D.add 0 (-a)).inv.app X =
        eqToHom h₀ := by
    rw [show z = D.zero.inv.app X by rfl, D.zero_add_inv_app]
    rw [← Category.assoc]
    have hcancel := congrArg (D.F (-a)).map
      (D.zero.inv_hom_id_app X)
    rw [Functor.map_comp] at hcancel
    rw [hcancel, (D.F (-a)).map_id, Category.id_comp]
  have hNzero :
      (D.F (-a) ⋙ N₀.obj).map z ≫
          N₀.obj.map ((D.add 0 (-a)).inv.app X) =
        N₀.obj.map (eqToHom h₀) := by
    have hn := congrArg N₀.obj.map hzero
    simpa only [Functor.comp_map, N₀.obj.map_comp] using hn
  have hcat' :
      M₀.obj.map z ≫ f.hom.app ((D.F 0).obj X) ≫
          U.hom.app ((D.F 0).obj X) ≫
            N₀.obj.map ((D.add 0 (-a)).inv.app X) =
        f.hom.app ((Functor.id C).obj X) ≫
          U.hom.app ((Functor.id C).obj X) ≫
            N₀.obj.map (eqToHom h₀) := by
    rw [hcat]
    rw [hNzero]
  have happly := congr($(hcat') x)
  simp only [ModuleCat.comp_apply] at happly
  change U.inv.app ((Functor.id C).obj X)
      (castZeroAdd
        (N₀.obj.map ((D.add 0 (-a)).inv.app X)
          (U.hom.app ((D.F 0).obj X)
            (f.hom.app ((D.F 0).obj X)
              (M₀.obj.map z x))))) =
    f.hom.app ((Functor.id C).obj X) x
  have hcast :
      castZeroAdd
          (N₀.obj.map (eqToHom h₀)
            (U.hom.app ((Functor.id C).obj X)
              (f.hom.app ((Functor.id C).obj X) x))) =
        U.hom.app ((Functor.id C).obj X)
          (f.hom.app ((Functor.id C).obj X) x) := by
    change e ▸
        (N₀.obj.map
          (eqToHom (congrArg (fun b ↦ (D.F b).obj X) e.symm))
            (U.hom.app ((Functor.id C).obj X)
              (f.hom.app ((Functor.id C).obj X) x))) = _
    exact moduleMap_eqToHom_cast N₀.obj
      (fun b ↦ (D.F b).obj X) e _
  calc
    _ = U.inv.app ((Functor.id C).obj X)
        (castZeroAdd
          (N₀.obj.map (eqToHom h₀)
            (U.hom.app ((Functor.id C).obj X)
              (f.hom.app ((Functor.id C).obj X) x)))) := by
      apply congrArg (U.inv.app ((Functor.id C).obj X))
      apply congrArg castZeroAdd
      exact happly
    _ = U.inv.app ((Functor.id C).obj X)
        (U.hom.app ((Functor.id C).obj X)
          (f.hom.app ((Functor.id C).obj X) x)) :=
      congrArg (U.inv.app ((Functor.id C).obj X)) hcast
    _ = _ := by
      simpa only [ModuleCat.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using
          congr($(U.hom_inv_id_app ((Functor.id C).obj X))
            (f.hom.app ((Functor.id C).obj X) x))

/-- Extraction in the same degree is a left inverse to homogeneous descent. -/
theorem linearModuleOrbitPushdownDegree_map
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ∀ (f : ShiftHom M₀ N₀ a),
      linearModuleOrbitPushdownDegree D M₀ N₀ a
          ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).map f ≫
            (linearModuleOrbitPushdownCommShiftIso (k := k) D a).hom.app N₀) =
        f := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  classical
  intro f
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv.app X
      (DirectSum.component k A
        (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (-a)
        (shiftedOrbitPushdownValueEquiv D N₀ a X
          (orbitPushdownNatTransAppLinear (A := A) f.hom X
            (orbitPushdownLof M₀.obj X 0
              (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))))) =
      f.hom.app X x
  exact linearModuleOrbitPushdownDegreeValue_map D M₀ N₀ a f X x

set_option backward.isDefEq.respectTransparency false in
/-- Extraction in any other degree vanishes after homogeneous descent. -/
theorem linearModuleOrbitPushdownDegree_map_ne
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    {a b : A} (hab : b ≠ a) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ∀ (f : ShiftHom M₀ N₀ a),
      linearModuleOrbitPushdownDegree D M₀ N₀ b
          ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).map f ≫
            (linearModuleOrbitPushdownCommShiftIso (k := k) D a).hom.app N₀) =
        0 := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  classical
  intro f
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    (linearModuleShiftUnderlyingIso (k := k) D N₀ b).inv.app X
      (DirectSum.component k A
        (fun c ↦ N₀.obj.obj ((D.F c).obj X)) (-b)
        (shiftedOrbitPushdownValueEquiv D N₀ a X
          (orbitPushdownNatTransAppLinear (A := A) f.hom X
            (orbitPushdownLof M₀.obj X 0
              (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))))) = 0
  rw [orbitPushdownNatTransAppLinear_lof]
  change
    (linearModuleShiftUnderlyingIso (k := k) D N₀ b).inv.app X
      (DirectSum.component k A
        (fun c ↦ N₀.obj.obj ((D.F c).obj X)) (-b)
        (shiftedOrbitPushdownValueEquiv D N₀ a X
          (orbitPushdownLof
            ((IsLinearModule (C := C) k).ι.obj (N₀⟦a⟧)) X 0
            (f.hom.app ((D.F 0).obj X)
              (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))))) = 0
  rw [shiftedOrbitPushdownValueEquiv_lof]
  have hneg : 0 + -a ≠ -b := by
    simp only [zero_add]
    intro h
    exact hab (neg_injective h.symm)
  change
    (linearModuleShiftUnderlyingIso (k := k) D N₀ b).inv.app X
      (DirectSum.component k A
        (fun c ↦ N₀.obj.obj ((D.F c).obj X)) (-b)
        (DirectSum.lof k A
          (fun c ↦ N₀.obj.obj ((D.F c).obj X)) (0 + -a) _)) = 0
  rw [DirectSum.component.of]
  simp only [dif_neg hneg]
  exact (linearModuleShiftUnderlyingIso (k := k) D N₀ b).inv.app X |>.hom.map_zero

/-- The linear synthesis map in Gabriel's Hom formula. -/
noncomputable def linearModuleOrbitPushdownSynthesisLinear
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := linearModuleCategoryAdditiveShift (R := k) D
    letI := linearModuleCategoryLinearShift (R := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ShiftOrbitHom A M₀ N₀ →ₗ[k]
      ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀ ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := linearModuleCategoryAdditiveShift (R := k) D
  letI := linearModuleCategoryLinearShift (R := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  exact (linearModuleOrbitPushdownDescended (R := k) D).mapLinearMap k

set_option backward.isDefEq.respectTransparency false in
/-- Synthesis in Gabriel's Hom formula respects shift-orbit convolution. -/
theorem linearModuleOrbitPushdownSynthesisLinear_comp
    (M N Z : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := linearModuleCategoryAdditiveShift (R := k) D
    letI := linearModuleCategoryLinearShift (R := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ∀ (f : ShiftOrbitHom A M N) (g : ShiftOrbitHom A N Z),
      linearModuleOrbitPushdownSynthesisLinear D M N f ≫
          linearModuleOrbitPushdownSynthesisLinear D N Z g =
        linearModuleOrbitPushdownSynthesisLinear D M Z
          (shiftOrbitCompHom f g) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := linearModuleCategoryAdditiveShift (R := k) D
  letI := linearModuleCategoryLinearShift (R := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  intro f g
  change (linearModuleOrbitPushdownDescended (R := k) D).map f ≫
      (linearModuleOrbitPushdownDescended (R := k) D).map g =
    (linearModuleOrbitPushdownDescended (R := k) D).map
      (shiftOrbitCompHom f g)
  rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On the degree-zero inclusion of an ordinary upstairs map, synthesis is
exactly the original push-down functor map. -/
theorem linearModuleOrbitPushdownSynthesisLinear_zero
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := linearModuleCategoryAdditiveShift (R := k) D
    letI := linearModuleCategoryLinearShift (R := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ∀ (f : M₀ ⟶ N₀),
      linearModuleOrbitPushdownSynthesisLinear D M₀ N₀
          (shiftOrbitOf M₀ N₀ 0 (shiftHomZero (A := A) f)) =
        (linearModuleOrbitPushdown
          (k := k) (C := C) (A := A)).map f := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := linearModuleCategoryAdditiveShift (R := k) D
  letI := linearModuleCategoryLinearShift (R := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  intro f
  change (linearModuleOrbitPushdownDescended (R := k) D).map
      (shiftOrbitOf M₀ N₀ 0 (shiftHomZero (A := A) f)) = _
  rw [linearModuleOrbitPushdownDescended_map_of]
  let P := linearModuleOrbitPushdown (k := k) (C := C) (A := A)
  letI := linearModuleOrbitPushdownCommShift (k := k) D
  change CategoryTheory.ShiftedHom.map (shiftHomZero (A := A) f) P =
    P.map f
  unfold shiftHomZero
  rw [CategoryTheory.ShiftedHom.map_mk₀]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Extracting all degrees after synthesis recovers a finite-support orbit
morphism. -/
theorem linearModuleOrbitPushdownDegrees_synthesis
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := linearModuleCategoryAdditiveShift (R := k) D
    letI := linearModuleCategoryLinearShift (R := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ∀ f : ShiftOrbitHom A M₀.obj N₀,
      linearModuleOrbitPushdownDegrees D M₀ N₀
          (linearModuleOrbitPushdownSynthesisLinear D M₀.obj N₀ f) =
        f := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := linearModuleCategoryAdditiveShift (R := k) D
  letI := linearModuleCategoryLinearShift (R := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  classical
  intro f
  refine DirectSum.induction_on f ?_ ?_ ?_
  · exact (linearModuleOrbitPushdownDegreesLinear D M₀ N₀).map_zero
  · intro a fa
    apply DirectSum.ext
    intro b
    rw [linearModuleOrbitPushdownDegrees_apply]
    change linearModuleOrbitPushdownDegree D M₀.obj N₀ b
        ((linearModuleOrbitPushdownDescended (R := k) D).map
          (shiftOrbitOf M₀.obj N₀ a fa)) = _
    rw [linearModuleOrbitPushdownDescended_map_of]
    by_cases hba : b = a
    · subst b
      rw [linearModuleOrbitPushdownDegree_map]
      exact (DirectSum.of_eq_same a fa).symm
    · rw [linearModuleOrbitPushdownDegree_map_ne D M₀.obj N₀ hba fa]
      exact (DirectSum.of_eq_of_ne a b fa hba).symm
  · intro f g hf hg
    exact (congrArg (linearModuleOrbitPushdownDegrees D M₀ N₀)
      ((linearModuleOrbitPushdownSynthesisLinear D M₀.obj N₀).map_add
        f g)).trans
          (((linearModuleOrbitPushdownDegreesLinear D M₀ N₀).map_add
            ((linearModuleOrbitPushdownSynthesisLinear D M₀.obj N₀) f)
            ((linearModuleOrbitPushdownSynthesisLinear D M₀.obj N₀) g)).trans
              (congrArg₂ (.+.) hf hg))

variable (M : CategoryTheory.Functor C (ModuleCat.{uM} k))
variable [M.Additive] [M.Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical orbit arrow from a shifted object sends its normalized
degree-zero inclusion to the corresponding homogeneous inclusion. -/
theorem orbitPushdownFromShift_zero_lof
    (X : C) (b : A) (x : M.obj ((D.F b).obj X)) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    orbitPushdownMapLinear M (shiftOrbitFromShift X b)
        (orbitPushdownLof M ((D.F b).obj X) 0
          (M.map (D.zero.inv.app ((D.F b).obj X)) x)) =
      orbitPushdownLof M X b x := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  let x₀ : M.obj ((Functor.id C).obj ((D.F b).obj X)) := x
  rw [shiftOrbitFromShift, orbitPushdownMapLinear_of]
  change
    orbitPushdownHomogeneousMap M b (𝟙 ((D.F b).obj X))
        (orbitPushdownLof M ((D.F b).obj X) 0
          (M.map (D.zero.inv.app ((D.F b).obj X)) x₀)) =
      orbitPushdownLof M X b x₀
  rw [orbitPushdownHomogeneousMap_lof]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_zero b)
  apply (orbitPushdownComponent_apply_heq_component'_apply M
    (add_zero b) (𝟙 ((D.F b).obj X))
      (M.map (D.zero.inv.app ((D.F b).obj X)) x)).trans
  apply heq_of_eq
  change M.map
      (orbitPushdownArrow' (add_zero b) (𝟙 ((D.F b).obj X)))
        (M.map (D.zero.inv.app ((D.F b).obj X)) x) = x
  simp only [orbitPushdownArrow', shiftFunctorAdd'_add_zero_inv_app]
  rw [(shiftFunctor C 0).map_id, Category.id_comp]
  change M.map
      (D.zero.hom.app ((D.F b).obj X))
        (M.map (D.zero.inv.app ((D.F b).obj X)) x) = x
  change (M.map (D.zero.inv.app ((D.F b).obj X)) ≫
    M.map (D.zero.hom.app ((D.F b).obj X))) x = x
  rw [← M.map_comp, Iso.inv_hom_id_app, M.map_id]
  rfl

variable {M N : CategoryTheory.Functor C (ModuleCat.{uM} k)}
variable [M.Additive] [M.Linear k] [N.Additive] [N.Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- A transformation between orbit push-downs is determined by its values on
the normalized degree-zero inclusions at all upstairs objects. -/
theorem orbitPushdownNatTrans_ext_zero
    : letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    ∀ (α β : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) N),
      (∀ (X : C) (x : M.obj X),
        α.app X
            (orbitPushdownLof M X 0
              (M.map ((shiftFunctorZero C A).inv.app X) x)) =
          β.app X
            (orbitPushdownLof M X 0
              (M.map ((shiftFunctorZero C A).inv.app X) x))) →
      α = β := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  intro α β hzero
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  let Y := (D.F b).obj X
  let q : ShiftOrbitHom A Y X := shiftOrbitFromShift (C := C) X b
  let z := orbitPushdownLof M Y 0
    (M.map ((shiftFunctorZero C A).inv.app Y) x)
  have hM : orbitPushdownMapLinear M q z =
      orbitPushdownLof M X b x :=
    orbitPushdownFromShift_zero_lof D M X b x
  have hα := congrArg (fun f ↦ f.hom z) (α.naturality q)
  have hβ := congrArg (fun f ↦ f.hom z) (β.naturality q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hα hβ
  change α.app X (orbitPushdownLof M X b x) =
    β.app X (orbitPushdownLof M X b x)
  calc
    _ = α.app X (orbitPushdownMapLinear M q z) :=
      congrArg (α.app X) hM.symm
    _ = orbitPushdownMapLinear N q (α.app Y z) := hα
    _ = orbitPushdownMapLinear N q (β.app Y z) := by
      apply congrArg (orbitPushdownMapLinear N q)
      exact hzero Y x
    _ = β.app X (orbitPushdownMapLinear M q z) := hβ.symm
    _ = _ := congrArg (β.app X) hM

set_option backward.isDefEq.respectTransparency false in
/-- The extracted shifted degree maps jointly determine a transformation
between orbit push-down modules. -/
theorem linearModuleOrbitPushdownDegree_jointlyFaithful
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (α β :
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀ ⟶
          (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀),
      (∀ a : A,
        linearModuleOrbitPushdownDegree D M₀ N₀ a α =
          linearModuleOrbitPushdownDegree D M₀ N₀ a β) →
      α = β := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  intro α β h
  apply ObjectProperty.hom_ext
  apply orbitPushdownNatTrans_ext_zero D α.hom β.hom
  intro X x
  apply DirectSum.ext
  intro c
  rw [show c = -(-c) by simp]
  change
    DirectSum.component k A
        (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (- -c)
        ((α.hom.app X).hom
          (orbitPushdownLof M₀.obj X 0
            (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))) =
      DirectSum.component k A
        (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (- -c)
        ((β.hom.app X).hom
          (orbitPushdownLof M₀.obj X 0
            (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x)))
  let a := -c
  let U := linearModuleShiftUnderlyingIso (k := k) D N₀ a
  have hdeg := congrArg (fun q ↦ q.hom) (h a)
  change orbitPushdownNatTransDegreeRaw D a α.hom ≫ U.inv =
    orbitPushdownNatTransDegreeRaw D a β.hom ≫ U.inv at hdeg
  have hraw : orbitPushdownNatTransDegreeRaw D a α.hom =
      orbitPushdownNatTransDegreeRaw D a β.hom := by
    apply (cancel_mono U.inv).mp
    exact hdeg
  have happ := NatTrans.congr_app hraw X
  have hx := congrArg (fun q ↦ q.hom x) happ
  change
    DirectSum.component k A
        (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (-a)
        ((α.hom.app X).hom
          (orbitPushdownLof M₀.obj X 0
            (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))) =
      DirectSum.component k A
        (fun b ↦ N₀.obj.obj ((D.F b).obj X)) (-a)
        ((β.hom.app X).hom
          (orbitPushdownLof M₀.obj X 0
            (M₀.obj.map ((shiftFunctorZero C A).inv.app X) x))) at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
/-- Synthesizing the extracted degrees recovers the original push-down
transformation. -/
theorem linearModuleOrbitPushdownSynthesis_degrees
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := linearModuleCategoryAdditiveShift (R := k) D
    letI := linearModuleCategoryLinearShift (R := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ∀ (α :
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀.obj ⟶
          (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀),
      linearModuleOrbitPushdownSynthesisLinear D M₀.obj N₀
          (linearModuleOrbitPushdownDegrees D M₀ N₀ α) =
        α := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := linearModuleCategoryAdditiveShift (R := k) D
  letI := linearModuleCategoryLinearShift (R := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  classical
  intro α
  apply linearModuleOrbitPushdownDegree_jointlyFaithful D
  intro a
  have h := linearModuleOrbitPushdownDegrees_synthesis D M₀ N₀
    (linearModuleOrbitPushdownDegrees D M₀ N₀ α)
  have ha := congrArg (fun f ↦ f a) h
  simpa only [linearModuleOrbitPushdownDegrees_apply] using ha

/-- Gabriel's Hom formula for the orbit push-down: finite-support shifted
upstairs maps are linearly equivalent to transformations downstairs. -/
noncomputable def linearModuleOrbitPushdownHomLinearEquiv
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := linearModuleCategoryAdditiveShift (R := k) D
    letI := linearModuleCategoryLinearShift (R := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    ShiftOrbitHom A M₀.obj N₀ ≃ₗ[k]
      ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀.obj ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := linearModuleCategoryAdditiveShift (R := k) D
  letI := linearModuleCategoryLinearShift (R := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  exact
    { toLinearMap := linearModuleOrbitPushdownSynthesisLinear D M₀.obj N₀
      invFun := linearModuleOrbitPushdownDegrees D M₀ N₀
      left_inv := linearModuleOrbitPushdownDegrees_synthesis D M₀ N₀
      right_inv := linearModuleOrbitPushdownSynthesis_degrees D M₀ N₀ }

end MagnitudeConjecture.CoveringHom
