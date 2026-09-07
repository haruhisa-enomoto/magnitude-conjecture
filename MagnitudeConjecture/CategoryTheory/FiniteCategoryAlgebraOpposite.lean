import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import MagnitudeConjecture.CategoryTheory.OppositeLinear

/-!
# Opposite algebras of finite linear categories

The finite category algebra built from covariant representables of `C` is
canonically isomorphic to the opposite of the corresponding algebra for
`Cᵒᵖ`.  The equivalence transposes the representable-summand matrix and sends
each canonical projector to the opposite of the matching projector.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]

noncomputable local instance finiteCategoryAlgebraOppositeFintype : Fintype Cᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

namespace finiteCategoryProjectiveGenerator

variable
    (hC : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hOp : ∀ X : Cᵒᵖ, IsFiniteDimensionalModule (C := Cᵒᵖ) k
      (linearCoyonedaLinearModule (k := k) X))

private abbrev repC (X : C) :=
  (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj (Opposite.op X)

private abbrev repOp (X : Cᵒᵖ) :=
  (finiteDimensionalLinearCoyonedaFunctor (k := k) hOp).obj (Opposite.op X)

private def transposeComponent (X Y : Cᵒᵖ)
    (f : repC hC Y.unop ⟶ repC hC X.unop) :
    repOp hOp X ⟶ repOp hOp Y :=
  ObjectProperty.homMk
    (linearCoyonedaHom (repOp hOp Y).obj X
      ((oppositeHomLinearEquiv (k := k) Y X).symm
        (f.hom.hom.app Y.unop (𝟙 Y.unop))))

private def untransposeComponent (X Y : Cᵒᵖ)
    (f : repOp hOp X ⟶ repOp hOp Y) :
    repC hC Y.unop ⟶ repC hC X.unop :=
  ObjectProperty.homMk
    (linearCoyonedaHom (repC hC X.unop).obj Y.unop
      (oppositeHomLinearEquiv (k := k) Y X
        (f.hom.hom.app X (𝟙 X))))

omit [Fintype C] in
private theorem untranspose_transpose (X Y : Cᵒᵖ)
    (f : repC hC Y.unop ⟶ repC hC X.unop) :
    untransposeComponent hC hOp X Y (transposeComponent hC hOp X Y f) = f := by
  apply ObjectProperty.hom_ext
  change linearCoyonedaHom (repC hC X.unop).obj Y.unop
      ((oppositeHomLinearEquiv (k := k) Y X)
        ((linearCoyonedaHom (repOp hOp Y).obj X
          ((oppositeHomLinearEquiv (k := k) Y X).symm
            (f.hom.hom.app Y.unop (𝟙 Y.unop)))).hom.app X (𝟙 X))) = f.hom
  rw [linearCoyonedaHom_app_id, LinearEquiv.apply_symm_apply]
  exact linearCoyonedaHom_self (repC hC X.unop).obj Y.unop f.hom

omit [Fintype C] in
private theorem transpose_untranspose (X Y : Cᵒᵖ)
    (f : repOp hOp X ⟶ repOp hOp Y) :
    transposeComponent hC hOp X Y (untransposeComponent hC hOp X Y f) = f := by
  apply ObjectProperty.hom_ext
  change linearCoyonedaHom (repOp hOp Y).obj X
      ((oppositeHomLinearEquiv (k := k) Y X).symm
        ((linearCoyonedaHom (repC hC X.unop).obj Y.unop
          (oppositeHomLinearEquiv (k := k) Y X
            (f.hom.hom.app X (𝟙 X)))).hom.app Y.unop (𝟙 Y.unop))) = f.hom
  rw [linearCoyonedaHom_app_id, LinearEquiv.symm_apply_apply]
  exact linearCoyonedaHom_self (repOp hOp Y).obj X f.hom

private def transposeComponentLinearEquiv (X Y : Cᵒᵖ) :
    (repC hC Y.unop ⟶ repC hC X.unop) ≃ₗ[k]
      (repOp hOp X ⟶ repOp hOp Y) where
  toFun := transposeComponent hC hOp X Y
  invFun := untransposeComponent hC hOp X Y
  left_inv := untranspose_transpose hC hOp X Y
  right_inv := transpose_untranspose hC hOp X Y
  map_add' f g := by
    apply ObjectProperty.hom_ext
    let a := f.hom.hom.app Y.unop (𝟙 Y.unop)
    let b := g.hom.hom.app Y.unop (𝟙 Y.unop)
    change linearCoyonedaHom (repOp hOp Y).obj X
        ((oppositeHomLinearEquiv (k := k) Y X).symm (a + b)) =
      linearCoyonedaHom (repOp hOp Y).obj X
          ((oppositeHomLinearEquiv (k := k) Y X).symm a) +
        linearCoyonedaHom (repOp hOp Y).obj X
          ((oppositeHomLinearEquiv (k := k) Y X).symm b)
    calc
      _ = linearCoyonedaHom (repOp hOp Y).obj X
          ((oppositeHomLinearEquiv (k := k) Y X).symm a +
            (oppositeHomLinearEquiv (k := k) Y X).symm b) :=
        congrArg _ ((oppositeHomLinearEquiv (k := k) Y X).symm.map_add a b)
      _ = _ := (linearCoyonedaHomEquiv (repOp hOp Y).obj X).symm.map_add _ _
  map_smul' r f := by
    apply ObjectProperty.hom_ext
    let a := f.hom.hom.app Y.unop (𝟙 Y.unop)
    change linearCoyonedaHom (repOp hOp Y).obj X
        ((oppositeHomLinearEquiv (k := k) Y X).symm
          (r • a)) =
      r • linearCoyonedaHom (repOp hOp Y).obj X
        ((oppositeHomLinearEquiv (k := k) Y X).symm
          a)
    calc
      _ = linearCoyonedaHom (repOp hOp Y).obj X
          (r • (oppositeHomLinearEquiv (k := k) Y X).symm a) :=
        congrArg _ ((oppositeHomLinearEquiv (k := k) Y X).symm.map_smul r a)
      _ = _ := (linearCoyonedaHomEquiv (repOp hOp Y).obj X).symm.map_smul r _

omit [Fintype C] in
private theorem transposeComponent_comp (X Y Z : Cᵒᵖ)
    (f : repC hC Z.unop ⟶ repC hC Y.unop)
    (g : repC hC Y.unop ⟶ repC hC X.unop) :
    transposeComponent hC hOp X Z (f ≫ g) =
      transposeComponent hC hOp X Y g ≫
        transposeComponent hC hOp Y Z f := by
  apply ObjectProperty.hom_ext
  change linearCoyonedaHom (repOp hOp Z).obj X
      ((oppositeHomLinearEquiv (k := k) Z X).symm
        ((f ≫ g).hom.hom.app Z.unop (𝟙 Z.unop))) =
    linearCoyonedaHom (repOp hOp Y).obj X
        ((oppositeHomLinearEquiv (k := k) Y X).symm
          (g.hom.hom.app Y.unop (𝟙 Y.unop))) ≫
      linearCoyonedaHom (repOp hOp Z).obj Y
        ((oppositeHomLinearEquiv (k := k) Z Y).symm
          (f.hom.hom.app Z.unop (𝟙 Z.unop)))
  rw [linearCoyonedaHom_comp]
  congr 1
  apply (oppositeHomLinearEquiv (k := k) Z X).injective
  simp only [LinearEquiv.apply_symm_apply]
  change g.hom.hom.app Z.unop
      (f.hom.hom.app Z.unop (𝟙 Z.unop)) =
    g.hom.hom.app Y.unop (𝟙 Y.unop) ≫
      f.hom.hom.app Z.unop (𝟙 Z.unop)
  let a := f.hom.hom.app Z.unop (𝟙 Z.unop)
  have hnat := ConcreteCategory.congr_hom (g.hom.hom.naturality a) (𝟙 Y.unop)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hnat
  change g.hom.hom.app Z.unop ((𝟙 Y.unop) ≫ a) =
    g.hom.hom.app Y.unop (𝟙 Y.unop) ≫ a at hnat
  simpa only [a, Category.id_comp] using hnat

private theorem algebra_components_comp
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (f g : algebra hP) (X Z : C) :
    biproduct.components (f ≫ g) X Z =
      ∑ Y : C, biproduct.components f X Y ≫ biproduct.components g Y Z := by
  classical
  let Q := fun X : C ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj (Opposite.op X)
  unfold biproduct.components
  change (biproduct.ι Q X ≫ f) ≫ g ≫ biproduct.π Q Z =
    ∑ Y : C, (biproduct.ι Q X ≫ f ≫ biproduct.π Q Y) ≫
      (biproduct.ι Q Y ≫ g ≫ biproduct.π Q Z)
  calc
    _ = biproduct.ι Q X ≫ f ≫ 𝟙 (⨁ Q) ≫
          g ≫ biproduct.π Q Z := by
      have hid : f ≫ 𝟙 (⨁ Q) = f := Category.comp_id f
      have h := congrArg
        (fun q ↦ biproduct.ι Q X ≫ q ≫ g ≫ biproduct.π Q Z) hid
      simpa only [Category.assoc] using h.symm
    _ = biproduct.ι Q X ≫ f ≫
          (∑ Y : C, biproduct.π Q Y ≫ biproduct.ι Q Y) ≫
          g ≫ biproduct.π Q Z := by rw [biproduct.total (f := Q)]
    _ = _ := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]

private def transposeEnd (f : algebra hC) : algebra hOp :=
  biproduct.matrix fun X Y ↦
    transposeComponent hC hOp X Y
      (biproduct.components f Y.unop X.unop)

private def untransposeEnd (f : algebra hOp) : algebra hC :=
  biproduct.matrix fun X Y ↦
    untransposeComponent hC hOp (Opposite.op Y) (Opposite.op X)
      (biproduct.components f (Opposite.op Y) (Opposite.op X))

private theorem untranspose_transpose_end (f : algebra hC) :
    untransposeEnd hC hOp (transposeEnd hC hOp f) = f := by
  apply (biproduct.matrixEquiv).injective
  funext X Y
  change biproduct.components
      (untransposeEnd hC hOp (transposeEnd hC hOp f)) X Y =
    biproduct.components f X Y
  simp only [untransposeEnd, transposeEnd, biproduct.matrix_components]
  exact untranspose_transpose hC hOp (Opposite.op Y) (Opposite.op X)
    (biproduct.components f X Y)

private theorem transpose_untranspose_end (f : algebra hOp) :
    transposeEnd hC hOp (untransposeEnd hC hOp f) = f := by
  apply (biproduct.matrixEquiv).injective
  funext X Y
  change biproduct.components
      (transposeEnd hC hOp (untransposeEnd hC hOp f)) X Y =
    biproduct.components f X Y
  simp only [untransposeEnd, transposeEnd, biproduct.matrix_components]
  simpa using transpose_untranspose hC hOp X Y (biproduct.components f X Y)

private def transposeEndLinearEquiv : algebra hC ≃ₗ[k] algebra hOp where
  toFun := transposeEnd hC hOp
  invFun := untransposeEnd hC hOp
  left_inv := untranspose_transpose_end hC hOp
  right_inv := transpose_untranspose_end hC hOp
  map_add' f g := by
    apply (biproduct.matrixEquiv).injective
    funext X Y
    change biproduct.components (transposeEnd hC hOp (f + g)) X Y =
      biproduct.components (transposeEnd hC hOp f + transposeEnd hC hOp g) X Y
    have htarget :
        biproduct.components (transposeEnd hC hOp f + transposeEnd hC hOp g) X Y =
          biproduct.components (transposeEnd hC hOp f) X Y +
            biproduct.components (transposeEnd hC hOp g) X Y := by
      unfold biproduct.components
      calc
        _ = (biproduct.ι _ X ≫ transposeEnd hC hOp f +
              biproduct.ι _ X ≫ transposeEnd hC hOp g) ≫ biproduct.π _ Y :=
          congrArg (fun z ↦ z ≫ biproduct.π _ Y)
            (Preadditive.comp_add _ _ _ (biproduct.ι _ X)
              (transposeEnd hC hOp f) (transposeEnd hC hOp g))
        _ = _ := Preadditive.add_comp _ _ _ _ _ _
    rw [htarget]
    simp only [transposeEnd, biproduct.matrix_components]
    have hsource :
        biproduct.components (f + g) Y.unop X.unop =
          biproduct.components f Y.unop X.unop +
            biproduct.components g Y.unop X.unop := by
      unfold biproduct.components
      calc
        _ = (biproduct.ι _ Y.unop ≫ f + biproduct.ι _ Y.unop ≫ g) ≫
              biproduct.π _ X.unop :=
          congrArg (fun z ↦ z ≫ biproduct.π _ X.unop)
            (Preadditive.comp_add _ _ _ (biproduct.ι _ Y.unop) f g)
        _ = _ := Preadditive.add_comp _ _ _ _ _ _
    rw [hsource]
    exact (transposeComponentLinearEquiv hC hOp X Y).map_add _ _
  map_smul' r f := by
    apply (biproduct.matrixEquiv).injective
    funext X Y
    change biproduct.components (transposeEnd hC hOp (r • f)) X Y =
      biproduct.components (r • transposeEnd hC hOp f) X Y
    have htarget :
        biproduct.components (r • transposeEnd hC hOp f) X Y =
          r • biproduct.components (transposeEnd hC hOp f) X Y := by
      unfold biproduct.components
      calc
        _ = (r • (biproduct.ι _ X ≫ transposeEnd hC hOp f)) ≫
              biproduct.π _ Y :=
          congrArg (fun z ↦ z ≫ biproduct.π _ Y)
            (CategoryTheory.Linear.comp_smul _ _ _
              (biproduct.ι _ X) r (transposeEnd hC hOp f))
        _ = _ := CategoryTheory.Linear.smul_comp _ _ _ _ _ _
    rw [htarget]
    simp only [transposeEnd, biproduct.matrix_components]
    have hsource :
        biproduct.components (r • f) Y.unop X.unop =
          r • biproduct.components f Y.unop X.unop := by
      unfold biproduct.components
      calc
        _ = (r • (biproduct.ι _ Y.unop ≫ f)) ≫ biproduct.π _ X.unop :=
          congrArg (fun z ↦ z ≫ biproduct.π _ X.unop)
            (CategoryTheory.Linear.comp_smul _ _ _ (biproduct.ι _ Y.unop) r f)
        _ = _ := CategoryTheory.Linear.smul_comp _ _ _ _ _ _
    rw [hsource]
    exact (transposeComponentLinearEquiv hC hOp X Y).map_smul r _

private theorem transposeEnd_comp (f g : algebra hC) :
    transposeEnd hC hOp (f ≫ g) =
      transposeEnd hC hOp g ≫ transposeEnd hC hOp f := by
  classical
  apply (biproduct.matrixEquiv).injective
  funext X Z
  change biproduct.components (transposeEnd hC hOp (f ≫ g)) X Z =
    biproduct.components (transposeEnd hC hOp g ≫ transposeEnd hC hOp f) X Z
  rw [algebra_components_comp hOp]
  simp only [transposeEnd, biproduct.matrix_components]
  rw [algebra_components_comp hC]
  change (transposeComponentLinearEquiv hC hOp X Z)
      (∑ Y : C, biproduct.components f Z.unop Y ≫
        biproduct.components g Y X.unop) =
    ∑ Y : Cᵒᵖ,
      transposeComponent hC hOp X Y
          (biproduct.components g Y.unop X.unop) ≫
        transposeComponent hC hOp Y Z
          (biproduct.components f Z.unop Y.unop)
  rw [map_sum]
  refine Fintype.sum_equiv Opposite.equivToOpposite _ _ ?_
  intro Y
  exact transposeComponent_comp hC hOp X (Opposite.op Y) Z
    (biproduct.components f Z.unop Y)
    (biproduct.components g Y X.unop)

private theorem transposeEnd_one :
    transposeEnd hC hOp (1 : algebra hC) = 1 := by
  let u := untransposeEnd hC hOp (1 : algebra hOp)
  have hu : transposeEnd hC hOp u = (1 : algebra hOp) :=
    transpose_untranspose_end hC hOp 1
  have hcomp :
      transposeEnd hC hOp (1 : algebra hC) ≫ transposeEnd hC hOp u =
        transposeEnd hC hOp (u ≫ (1 : algebra hC)) :=
    (transposeEnd_comp hC hOp u (1 : algebra hC)).symm
  have hright :
      transposeEnd hC hOp (1 : algebra hC) ≫ transposeEnd hC hOp u =
        transposeEnd hC hOp u :=
    hcomp.trans (congrArg (transposeEnd hC hOp) (Category.comp_id u))
  rw [hu] at hright
  apply End.ext
  simpa only [End.one_def, Category.comp_id] using hright

private def categoryAlgebraOppositeLinearEquiv :
    algebra hC ≃ₗ[k] (algebra hOp)ᵐᵒᵖ :=
  (transposeEndLinearEquiv hC hOp).trans (MulOpposite.opLinearEquiv k)

def categoryAlgebraOppositeEquiv :
    algebra hC ≃ₐ[k] (algebra hOp)ᵐᵒᵖ :=
  AlgEquiv.ofLinearEquiv (categoryAlgebraOppositeLinearEquiv hC hOp)
    (by
      change MulOpposite.op (transposeEnd hC hOp 1) = 1
      rw [transposeEnd_one]
      rfl)
    (by
      intro f g
      change MulOpposite.op (transposeEnd hC hOp (f * g)) =
        MulOpposite.op (transposeEnd hC hOp f) *
          MulOpposite.op (transposeEnd hC hOp g)
      apply MulOpposite.unop_injective
      rw [MulOpposite.unop_mul]
      change transposeEnd hC hOp (g ≫ f) =
        transposeEnd hC hOp g * transposeEnd hC hOp f
      rw [transposeEnd_comp, End.mul_def])

omit [Fintype C] in
@[simp] private theorem transposeComponent_zero (X Y : Cᵒᵖ) :
    transposeComponent hC hOp X Y 0 = 0 :=
  (transposeComponentLinearEquiv hC hOp X Y).map_zero

omit [Fintype C] in
@[simp] private theorem transposeComponent_id (X : Cᵒᵖ) :
    transposeComponent hC hOp X X (𝟙 (repC hC X.unop)) =
      𝟙 (repOp hOp X) := by
  apply ObjectProperty.hom_ext
  change linearCoyonedaHom (repOp hOp X).obj X
      ((oppositeHomLinearEquiv (k := k) X X).symm (𝟙 X.unop)) =
    𝟙 (repOp hOp X).obj
  have hid :
      (oppositeHomLinearEquiv (k := k) X X).symm (𝟙 X.unop) = 𝟙 X := by
    apply Quiver.Hom.unop_inj
    rfl
  rw [hid]
  exact linearCoyonedaHom_self (repOp hOp X).obj X (𝟙 (repOp hOp X).obj)

private theorem canonicalProjector_components_self
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) (X : C) :
    biproduct.components (canonicalProjector hP X) X X =
      𝟙 ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X)) := by
  let Q := fun Y : C ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj (Opposite.op Y)
  change (biproduct.ι Q X ≫ biproduct.π Q X) ≫
      (biproduct.ι Q X ≫ biproduct.π Q X) = 𝟙 (Q X)
  simp

private theorem canonicalProjector_components_eq_zero_of_row_ne
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    {X Y : C} (Z : C) (hYX : Y ≠ X) :
    biproduct.components (canonicalProjector hP X) Y Z = 0 := by
  let Q := fun W : C ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj (Opposite.op W)
  change (biproduct.ι Q Y ≫ biproduct.π Q X) ≫
      (biproduct.ι Q X ≫ biproduct.π Q Z) = 0
  rw [biproduct.ι_π_ne Q hYX]
  simp

private theorem canonicalProjector_components_eq_zero_of_column_ne
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (Y : C) {X Z : C} (hXZ : X ≠ Z) :
    biproduct.components (canonicalProjector hP X) Y Z = 0 := by
  let Q := fun W : C ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj (Opposite.op W)
  change (biproduct.ι Q Y ≫ biproduct.π Q X) ≫
      (biproduct.ι Q X ≫ biproduct.π Q Z) = 0
  rw [biproduct.ι_π_ne Q hXZ]
  simp

theorem categoryAlgebraOppositeEquiv_canonicalProjector (X : C) :
    categoryAlgebraOppositeEquiv hC hOp
        (canonicalProjector hC X) =
      MulOpposite.op (canonicalProjector hOp (Opposite.op X)) := by
  apply MulOpposite.unop_injective
  change transposeEnd hC hOp (canonicalProjector hC X) =
    canonicalProjector hOp (Opposite.op X)
  apply (biproduct.matrixEquiv).injective
  funext Y Z
  change biproduct.components
      (transposeEnd hC hOp (canonicalProjector hC X)) Y Z =
    biproduct.components (canonicalProjector hOp (Opposite.op X)) Y Z
  simp only [transposeEnd, biproduct.matrix_components]
  by_cases hY : Y = Opposite.op X
  · subst Y
    by_cases hZ : Z = Opposite.op X
    · subst Z
      rw [canonicalProjector_components_self hC X,
        canonicalProjector_components_self hOp (Opposite.op X)]
      exact transposeComponent_id hC hOp (Opposite.op X)
    · have hZu : Z.unop ≠ X := by
        intro h
        apply hZ
        exact Opposite.unop_injective h
      rw [canonicalProjector_components_eq_zero_of_row_ne hC X hZu,
        canonicalProjector_components_eq_zero_of_column_ne hOp
          (Opposite.op X) (Ne.symm hZ)]
      exact transposeComponent_zero hC hOp (Opposite.op X) Z
  · by_cases hZ : Z = Opposite.op X
    · subst Z
      have hYu : Y.unop ≠ X := by
        intro h
        apply hY
        exact Opposite.unop_injective h
      rw [canonicalProjector_components_eq_zero_of_column_ne hC X (Ne.symm hYu),
        canonicalProjector_components_eq_zero_of_row_ne hOp
          (Opposite.op X) hY]
      exact transposeComponent_zero hC hOp Y (Opposite.op X)
    · have hYu : Y.unop ≠ X := by
        intro h
        apply hY
        exact Opposite.unop_injective h
      have hZu : Z.unop ≠ X := by
        intro h
        apply hZ
        exact Opposite.unop_injective h
      rw [canonicalProjector_components_eq_zero_of_row_ne hC Y.unop hZu,
        canonicalProjector_components_eq_zero_of_row_ne hOp Z hY]
      exact transposeComponent_zero hC hOp Y Z

end finiteCategoryProjectiveGenerator
end MagnitudeConjecture.CoveringHom
