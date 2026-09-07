import MagnitudeConjecture.Algebra.RightModulePrimitiveProjectiveCoordinates
import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverLiftedPresentation

/-!
# The basic algebra of a complete primitive-projective presentation

For a complete family of primitive idempotents in `A`, the finite category
algebra formed from covariant representables of the selected right
projectives is canonically `Aᵐᵒᵖ`.  The opposite is forced by variance:
covariant Yoneda is defined on the opposite of the projective category.

The matrix calculation is carried out on the original small selected-
projective category.  Its category algebra is then transported to the
universe-lifted copy used by the ordinary-quiver presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

noncomputable instance projectiveCategoryFintype :
    Fintype S.ProjectiveCategory :=
  inferInstanceAs (Fintype S.ProjectiveLabel)

/-- Forget the induced-category type synonym on a selected projective. -/
def projectiveCategoryLabel (X : S.ProjectiveCategory) : S.ProjectiveLabel :=
  X

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem projectiveCategoryLabel_injective :
    Function.Injective S.projectiveCategoryLabel := by
  intro X Y hXY
  exact hXY

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Covariant representables of the small selected-projective category are
finite-dimensional and finitely supported. -/
theorem projectiveCategory_finiteRepresentables :
    ∀ X : S.ProjectiveCategory,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.ProjectiveCategory) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  intro X
  constructor
  · intro Y
    let inclusion : (X ⟶ Y) →ₗ[k]
        (S.fgObj X.label ⟶ S.fgObj Y.label) :=
      { toFun := fun f ↦ f.hom
        map_add' := by
          intro f g
          rfl
        map_smul' := by
          intro r f
          rfl }
    apply Module.Finite.of_injective inclusion
    intro f g hfg
    apply InducedCategory.hom_ext
    exact hfg
  · exact Set.toFinite _

/-- Lift a selected projective and its morphisms to the universe-local copy
used by the ordinary-quiver presentation. -/
def projectiveToLifted :
    S.ProjectiveCategory ⥤ S.LiftedProjectiveCategory where
  obj X := ⟨ULift.up X⟩
  map f := InducedCategory.homMk f
  map_id X := by
    apply InducedCategory.hom_ext
    rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    rfl

noncomputable instance projectiveToLifted_additive :
    S.projectiveToLifted.Additive where
  map_add := by
    intro X Y f g
    apply InducedCategory.hom_ext
    rfl

noncomputable instance projectiveToLifted_linear :
    S.projectiveToLifted.Linear k where
  map_smul := by
    intro X Y f r
    apply InducedCategory.hom_ext
    rfl

noncomputable instance projectiveToLifted_full :
    S.projectiveToLifted.Full where
  map_surjective {X Y} f := by
    exact ⟨f.hom, by
      apply InducedCategory.hom_ext
      rfl⟩

noncomputable instance projectiveToLifted_faithful :
    S.projectiveToLifted.Faithful where
  map_injective {X Y} f g h := by
    exact congrArg InducedCategory.Hom.hom h

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem projectiveToLifted_obj_bijective :
    Function.Bijective S.projectiveToLifted.obj := by
  constructor
  · rintro X Y hXY
    have hvertex := congrArg LiftedProjectiveLabel.vertex hXY
    exact congrArg ULift.down hvertex
  · rintro ⟨⟨X⟩⟩
    exact ⟨S.ordinaryProjectiveObj X, rfl⟩

noncomputable instance projectiveToLifted_essSurj :
    S.projectiveToLifted.EssSurj := by
  constructor
  intro Y
  obtain ⟨X, hX⟩ := S.projectiveToLifted_obj_bijective.2 Y
  exact ⟨X, ⟨eqToIso hX⟩⟩

/-- The small and lifted selected-projective categories are linearly
equivalent by literal object reindexing. -/
noncomputable def projectiveLiftedEquivalence :
    S.ProjectiveCategory ≌ S.LiftedProjectiveCategory := by
  let F := S.projectiveToLifted
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

noncomputable instance projectiveLiftedEquivalence_functor_additive :
    S.projectiveLiftedEquivalence.functor.Additive := by
  change S.projectiveToLifted.Additive
  infer_instance

noncomputable instance projectiveLiftedEquivalence_functor_linear :
    S.projectiveLiftedEquivalence.functor.Linear k := by
  change S.projectiveToLifted.Linear k
  infer_instance

/-- Objectwise universe lifting identifies the small and lifted selected-
projective category algebras. -/
noncomputable def projectiveCategoryAlgebraEquiv :
    CoveringHom.finiteCategoryProjectiveGenerator.algebra
        S.projectiveCategory_finiteRepresentables ≃ₐ[k]
      S.basicAlgebra :=
  CoveringHom.finiteCategoryAlgebraEquiv
    (C := S.ProjectiveCategory) (D := S.LiftedProjectiveCategory)
    S.projectiveCategory_finiteRepresentables
    S.liftedProjectiveCategory_finiteRepresentables
    S.projectiveLiftedEquivalence
    S.projectiveToLifted_obj_bijective

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- The selected-projective morphism represented by the two-sided
idempotent component `e_X a e_Y`. -/
def projectiveComponent (a : A) (X Y : S.ProjectiveCategory) : Y ⟶ X :=
  P.projectiveHomOfCoordinate
    (p := S.projectiveCategoryLabel Y)
    (q := S.projectiveCategoryLabel X)
    (P.idempotent (S.projectiveCategoryLabel X) * a *
      P.idempotent (S.projectiveCategoryLabel Y))
    (by
      simp only [← mul_assoc]
      rw [(P.complete.idem (S.projectiveCategoryLabel X)).eq])
    (by
      simp only [mul_assoc]
      rw [(P.complete.idem (S.projectiveCategoryLabel Y)).eq])

@[simp]
theorem projectiveHomCoordinate_projectiveComponent
    (a : A) (X Y : S.ProjectiveCategory) :
    P.projectiveHomCoordinate (P.projectiveComponent a X Y) =
      P.idempotent (S.projectiveCategoryLabel X) * a *
        P.idempotent (S.projectiveCategoryLabel Y) := by
  simp only [projectiveComponent,
    P.projectiveHomCoordinate_projectiveHomOfCoordinate]

private abbrev F :=
  CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k)
    S.projectiveCategory_finiteRepresentables

omit [IsNoetherianRing Aᵐᵒᵖ] in
private theorem F_map_op_smul
    {X Y : S.ProjectiveCategory} (r : k) (f : X ⟶ Y) :
    (F (k := k) (S := S)).map (r • f).op =
      r • (F (k := k) (S := S)).map f.op := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change (r • f) ≫ q = r • (f ≫ q)
  simp

private abbrev Q (X : S.ProjectiveCategory) :=
  (F (k := k) (S := S)).obj (Opposite.op X)

private abbrev smallProjectiveGenerator :=
  ⨁ fun X : S.ProjectiveCategory ↦ Q (k := k) (S := S) X

private abbrev smallBasicAlgebra :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra
    S.projectiveCategory_finiteRepresentables

private def smallComponentMatrix (a : A) :
    smallBasicAlgebra (k := k) (S := S) :=
  biproduct.matrix fun X Y ↦
    (F (k := k) (S := S)).map (P.projectiveComponent a X Y).op

@[simp]
private theorem smallComponentMatrix_components (a : A)
    (X Y : S.ProjectiveCategory) :
    biproduct.components (P.smallComponentMatrix a) X Y =
      (F (k := k) (S := S)).map (P.projectiveComponent a X Y).op := by
  rw [smallComponentMatrix, biproduct.matrix_components]

@[simp]
private theorem projectiveComponent_zero (X Y : S.ProjectiveCategory) :
    P.projectiveComponent 0 X Y = 0 := by
  apply P.projectiveHomCoordinate_injective
    (S.projectiveCategoryLabel Y) (S.projectiveCategoryLabel X)
  change P.projectiveHomCoordinate (P.projectiveComponent 0 X Y) =
    P.projectiveHomCoordinate
      (0 : Y ⟶ X)
  rw [projectiveHomCoordinate_projectiveComponent,
    P.projectiveHomCoordinate_zero]
  simp

@[simp]
private theorem projectiveComponent_add (a b : A)
    (X Y : S.ProjectiveCategory) :
    P.projectiveComponent (a + b) X Y =
      P.projectiveComponent a X Y + P.projectiveComponent b X Y := by
  apply P.projectiveHomCoordinate_injective
    (S.projectiveCategoryLabel Y) (S.projectiveCategoryLabel X)
  change P.projectiveHomCoordinate (P.projectiveComponent (a + b) X Y) =
    P.projectiveHomCoordinate
      (P.projectiveComponent a X Y + P.projectiveComponent b X Y)
  rw [projectiveHomCoordinate_projectiveComponent,
    P.projectiveHomCoordinate_add,
    projectiveHomCoordinate_projectiveComponent,
    projectiveHomCoordinate_projectiveComponent]
  rw [mul_add, add_mul]

private theorem projectiveHomCoordinate_sum
    {X Y : S.ProjectiveCategory} {ι : Type*} (s : Finset ι)
    (f : ι → (X ⟶ Y)) :
    P.projectiveHomCoordinate (∑ i ∈ s, f i) =
      ∑ i ∈ s, P.projectiveHomCoordinate (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P.projectiveHomCoordinate_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [P.projectiveHomCoordinate_add, ih]

private theorem projectiveHomCoordinate_id_projectiveCategory
    (X : S.ProjectiveCategory) :
    P.projectiveHomCoordinate (𝟙 X) =
      P.idempotent (S.projectiveCategoryLabel X) := by
  change P.projectiveHomCoordinate
      (𝟙 (S.ordinaryProjectiveObj (S.projectiveCategoryLabel X))) = _
  exact P.projectiveHomCoordinate_id (S.projectiveCategoryLabel X)

omit [IsNoetherianRing Aᵐᵒᵖ] in
private theorem smallBasicAlgebra_components_comp
    (f g : smallBasicAlgebra (k := k) (S := S))
    (X Y : S.ProjectiveCategory) :
    biproduct.components (f ≫ g) X Y =
      ∑ Z : S.ProjectiveCategory,
        biproduct.components f X Z ≫ biproduct.components g Z Y := by
  let Q' := fun X : S.ProjectiveCategory ↦ Q (k := k) (S := S) X
  unfold biproduct.components
  change (biproduct.ι Q' X ≫ f) ≫ g ≫ biproduct.π Q' Y = _
  calc
    _ = biproduct.ι Q' X ≫ f ≫ 𝟙 (⨁ Q') ≫ g ≫
          biproduct.π Q' Y := by
        have hid : f ≫ 𝟙 (⨁ Q') = f := Category.comp_id f
        have h := congrArg
          (fun q ↦ biproduct.ι Q' X ≫ q ≫ g ≫ biproduct.π Q' Y) hid
        simpa only [Category.assoc] using h.symm
    _ = biproduct.ι Q' X ≫ f ≫
          (∑ Z : S.ProjectiveCategory,
            biproduct.π Q' Z ≫ biproduct.ι Q' Z) ≫ g ≫
              biproduct.π Q' Y := by rw [biproduct.total (f := Q')]
    _ = _ := by
      simp only [Q', Preadditive.comp_sum, Preadditive.sum_comp,
        Category.assoc]

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
private theorem smallBasicAlgebra_components_zero
    (X Y : S.ProjectiveCategory) :
    biproduct.components
      (0 : smallBasicAlgebra (k := k) (S := S)) X Y = 0 := by
  unfold biproduct.components
  simp

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
private theorem smallBasicAlgebra_components_add
    (f g : smallBasicAlgebra (k := k) (S := S))
    (X Y : S.ProjectiveCategory) :
    biproduct.components (f + g) X Y =
      biproduct.components f X Y + biproduct.components g X Y := by
  unfold biproduct.components
  change (biproduct.ι _ X ≫ End.asHom (f + g)) ≫ biproduct.π _ Y =
    (biproduct.ι _ X ≫ End.asHom f) ≫ biproduct.π _ Y +
      (biproduct.ι _ X ≫ End.asHom g) ≫ biproduct.π _ Y
  rw [show End.asHom (f + g) = End.asHom f + End.asHom g by rfl,
    Preadditive.comp_add, Preadditive.add_comp]

omit [IsNoetherianRing Aᵐᵒᵖ] in
private theorem smallBasicAlgebra_components_mul
    (f g : smallBasicAlgebra (k := k) (S := S))
    (X Y : S.ProjectiveCategory) :
    biproduct.components (f * g) X Y =
      ∑ Z : S.ProjectiveCategory,
        biproduct.components g X Z ≫ biproduct.components f Z Y := by
  change biproduct.components (g ≫ f) X Y = _
  exact smallBasicAlgebra_components_comp g f X Y

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
private theorem smallBasicAlgebra_components_smul
    (r : k) (f : smallBasicAlgebra (k := k) (S := S))
    (X Y : S.ProjectiveCategory) :
    biproduct.components (r • f) X Y =
      r • biproduct.components f X Y := by
  unfold biproduct.components
  change (biproduct.ι _ X ≫ (r • End.asHom f)) ≫ biproduct.π _ Y =
    r • ((biproduct.ι _ X ≫ End.asHom f) ≫ biproduct.π _ Y)
  rw [CategoryTheory.Linear.comp_smul, CategoryTheory.Linear.smul_comp]

private theorem sum_idempotent_projectiveCategory :
    ∑ X : S.ProjectiveCategory,
      P.idempotent (S.projectiveCategoryLabel X) = 1 := by
  change ∑ X : S.ProjectiveLabel, P.idempotent X = 1
  exact P.complete.complete

private theorem projectiveComponent_mul_sum (a b : A)
    (X Y : S.ProjectiveCategory) :
    P.projectiveComponent (b * a) X Y =
      ∑ Z : S.ProjectiveCategory,
        P.projectiveComponent a Z Y ≫ P.projectiveComponent b X Z := by
  apply P.projectiveHomCoordinate_injective
    (S.projectiveCategoryLabel Y) (S.projectiveCategoryLabel X)
  change P.projectiveHomCoordinate (P.projectiveComponent (b * a) X Y) =
    P.projectiveHomCoordinate
      (∑ Z : S.ProjectiveCategory,
        P.projectiveComponent a Z Y ≫ P.projectiveComponent b X Z)
  rw [projectiveHomCoordinate_projectiveComponent]
  have hcoordinateSum := P.projectiveHomCoordinate_sum Finset.univ
    (fun Z : S.ProjectiveCategory ↦
      P.projectiveComponent a Z Y ≫ P.projectiveComponent b X Z)
  rw [show P.projectiveHomCoordinate
      (∑ Z : S.ProjectiveCategory,
        P.projectiveComponent a Z Y ≫ P.projectiveComponent b X Z) =
      ∑ Z : S.ProjectiveCategory,
        P.projectiveHomCoordinate
          (P.projectiveComponent a Z Y ≫ P.projectiveComponent b X Z) by
    simpa using hcoordinateSum]
  simp only [P.projectiveHomCoordinate_comp,
    projectiveHomCoordinate_projectiveComponent]
  have hterm (Z : S.ProjectiveCategory) :
      (P.idempotent (S.projectiveCategoryLabel X) * b *
          P.idempotent (S.projectiveCategoryLabel Z)) *
          (P.idempotent (S.projectiveCategoryLabel Z) * a *
            P.idempotent (S.projectiveCategoryLabel Y)) =
        P.idempotent (S.projectiveCategoryLabel X) *
          (b * (P.idempotent (S.projectiveCategoryLabel Z) *
            (a * P.idempotent (S.projectiveCategoryLabel Y)))) := by
    simp only [mul_assoc]
    rw [← mul_assoc (P.idempotent (S.projectiveCategoryLabel Z))
      (P.idempotent (S.projectiveCategoryLabel Z))
      (a * P.idempotent (S.projectiveCategoryLabel Y)),
      (P.complete.idem (S.projectiveCategoryLabel Z)).eq]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [P.sum_idempotent_projectiveCategory]
  simp only [one_mul, mul_assoc]

private def toSmallBasicAlgebraAlgHom :
    Aᵐᵒᵖ →ₐ[k] smallBasicAlgebra (k := k) (S := S) where
  toFun a := P.smallComponentMatrix a.unop
  map_zero' := by
    apply (biproduct.matrixEquiv).injective
    funext X Y
    change biproduct.components
        (P.smallComponentMatrix (MulOpposite.unop 0)) X Y =
      biproduct.components
        (0 : smallBasicAlgebra (k := k) (S := S)) X Y
    rw [smallComponentMatrix_components,
      smallBasicAlgebra_components_zero]
    simp only [MulOpposite.unop_zero]
    rw [P.projectiveComponent_zero, op_zero,
      (F (k := k) (S := S)).map_zero]
  map_add' a b := by
    apply (biproduct.matrixEquiv).injective
    funext X Y
    change biproduct.components
        (P.smallComponentMatrix (MulOpposite.unop (a + b))) X Y =
      biproduct.components
        (P.smallComponentMatrix a.unop + P.smallComponentMatrix b.unop) X Y
    rw [smallComponentMatrix_components,
      smallBasicAlgebra_components_add,
      smallComponentMatrix_components, smallComponentMatrix_components]
    simp only [MulOpposite.unop_add]
    rw [P.projectiveComponent_add]
    exact (F (k := k) (S := S)).map_add
  map_one' := by
    apply (biproduct.matrixEquiv).injective
    funext X Y
    change biproduct.components
        (P.smallComponentMatrix (MulOpposite.unop 1)) X Y =
      biproduct.components
        (1 : smallBasicAlgebra (k := k) (S := S)) X Y
    rw [smallComponentMatrix_components]
    simp only [MulOpposite.unop_one]
    by_cases hXY : X = Y
    · subst Y
      have hcomponent : P.projectiveComponent 1 X X =
          𝟙 X := by
        apply P.projectiveHomCoordinate_injective
          (S.projectiveCategoryLabel X) (S.projectiveCategoryLabel X)
        change P.projectiveHomCoordinate (P.projectiveComponent 1 X X) =
          P.projectiveHomCoordinate (𝟙 X)
        rw [projectiveHomCoordinate_projectiveComponent,
          P.projectiveHomCoordinate_id_projectiveCategory]
        simpa using
          (P.complete.idem (S.projectiveCategoryLabel X)).eq
      rw [hcomponent, CategoryTheory.op_id,
        (F (k := k) (S := S)).map_id]
      symm
      simp [biproduct.components]
    · have hcomponent : P.projectiveComponent 1 X Y = 0 := by
        apply P.projectiveHomCoordinate_injective
          (S.projectiveCategoryLabel Y) (S.projectiveCategoryLabel X)
        change P.projectiveHomCoordinate (P.projectiveComponent 1 X Y) =
          P.projectiveHomCoordinate
            (0 : Y ⟶ X)
        rw [projectiveHomCoordinate_projectiveComponent,
          P.projectiveHomCoordinate_zero]
        simpa only [mul_one] using P.complete.ortho
          (fun h ↦ hXY (S.projectiveCategoryLabel_injective h))
      rw [hcomponent, op_zero,
        (F (k := k) (S := S)).map_zero]
      symm
      simp [biproduct.components, hXY]
  map_mul' a b := by
    apply (biproduct.matrixEquiv).injective
    funext X Y
    change biproduct.components
        (P.smallComponentMatrix (MulOpposite.unop (a * b))) X Y =
      biproduct.components
        (P.smallComponentMatrix a.unop * P.smallComponentMatrix b.unop) X Y
    rw [smallComponentMatrix_components, smallBasicAlgebra_components_mul]
    simp only [MulOpposite.unop_mul]
    simp_rw [smallComponentMatrix_components]
    rw [P.projectiveComponent_mul_sum, CategoryTheory.op_sum,
      (F (k := k) (S := S)).map_sum]
    apply Finset.sum_congr rfl
    intro Z hZ
    rw [CategoryTheory.op_comp, (F (k := k) (S := S)).map_comp]
  commutes' := by
    intro r
    apply (biproduct.matrixEquiv).injective
    funext X Y
    change biproduct.components
        (P.smallComponentMatrix
          (MulOpposite.unop (algebraMap k Aᵐᵒᵖ r))) X Y =
      biproduct.components
        (algebraMap k (smallBasicAlgebra (k := k) (S := S)) r) X Y
    rw [smallComponentMatrix_components]
    change (F (k := k) (S := S)).map
        (P.projectiveComponent (algebraMap k A r) X Y).op =
      biproduct.components
        (algebraMap k (smallBasicAlgebra (k := k) (S := S)) r) X Y
    by_cases hXY : X = Y
    · subst Y
      have hcomponent :
          P.projectiveComponent (algebraMap k A r) X X =
            r • 𝟙 X := by
        apply P.projectiveHomCoordinate_injective
          (S.projectiveCategoryLabel X) (S.projectiveCategoryLabel X)
        change P.projectiveHomCoordinate
            (P.projectiveComponent (algebraMap k A r) X X) =
          P.projectiveHomCoordinate (r • 𝟙 X)
        rw [projectiveHomCoordinate_projectiveComponent,
          P.projectiveHomCoordinate_smul,
          P.projectiveHomCoordinate_id_projectiveCategory]
        rw [← Algebra.commutes]
        simp only [Algebra.smul_def, mul_assoc]
        rw [(P.complete.idem (S.projectiveCategoryLabel X)).eq]
      rw [hcomponent, F_map_op_smul,
        CategoryTheory.op_id,
        (F (k := k) (S := S)).map_id]
      rw [Algebra.algebraMap_eq_smul_one]
      rw [smallBasicAlgebra_components_smul]
      simp [biproduct.components]
    · have hcomponent :
          P.projectiveComponent (algebraMap k A r) X Y = 0 := by
        apply P.projectiveHomCoordinate_injective
          (S.projectiveCategoryLabel Y) (S.projectiveCategoryLabel X)
        change P.projectiveHomCoordinate
            (P.projectiveComponent (algebraMap k A r) X Y) =
          P.projectiveHomCoordinate
            (0 : Y ⟶ X)
        rw [projectiveHomCoordinate_projectiveComponent,
          P.projectiveHomCoordinate_zero]
        rw [← Algebra.commutes]
        simp only [mul_assoc]
        rw [P.complete.ortho
          (fun h ↦ hXY (S.projectiveCategoryLabel_injective h)), mul_zero]
      rw [hcomponent, op_zero,
        (F (k := k) (S := S)).map_zero]
      rw [Algebra.algebraMap_eq_smul_one]
      rw [smallBasicAlgebra_components_smul]
      simp [biproduct.components, hXY]

/-- Recover the selected-projective morphism represented by one matrix
component. -/
private def componentPreimage
    (f : smallBasicAlgebra (k := k) (S := S))
    (X Y : S.ProjectiveCategory) : Y ⟶ X :=
  ((F (k := k) (S := S)).preimage (biproduct.components f X Y)).unop

/-- The ambient corner coordinate of one matrix component. -/
private def matrixCoordinate
    (f : smallBasicAlgebra (k := k) (S := S))
    (X Y : S.ProjectiveCategory) : A :=
  P.projectiveHomCoordinate (componentPreimage f X Y)

@[simp]
private theorem matrixCoordinate_smallComponentMatrix
    (a : A) (X Y : S.ProjectiveCategory) :
    P.matrixCoordinate (P.smallComponentMatrix a) X Y =
      P.idempotent (S.projectiveCategoryLabel X) * a *
        P.idempotent (S.projectiveCategoryLabel Y) := by
  simp only [matrixCoordinate, componentPreimage,
    smallComponentMatrix_components]
  rw [(F (k := k) (S := S)).preimage_map,
    Quiver.Hom.unop_op,
    projectiveHomCoordinate_projectiveComponent]

/-- Sum all corner coordinates of a matrix endomorphism. -/
private def fromSmallBasicAlgebra
    (f : smallBasicAlgebra (k := k) (S := S)) : Aᵐᵒᵖ :=
  MulOpposite.op
    (∑ X : S.ProjectiveCategory,
      ∑ Y : S.ProjectiveCategory, P.matrixCoordinate f X Y)

private theorem sum_all_corners (a : A) :
    (∑ X : S.ProjectiveCategory,
      ∑ Y : S.ProjectiveCategory,
        P.idempotent (S.projectiveCategoryLabel X) * a *
          P.idempotent (S.projectiveCategoryLabel Y)) = a := by
  calc
    _ = ∑ X : S.ProjectiveCategory,
          (P.idempotent (S.projectiveCategoryLabel X) * a) *
            (∑ Y : S.ProjectiveCategory,
              P.idempotent (S.projectiveCategoryLabel Y)) := by
        apply Finset.sum_congr rfl
        intro X hX
        rw [Finset.mul_sum]
    _ = ∑ X : S.ProjectiveCategory,
          P.idempotent (S.projectiveCategoryLabel X) * a := by
        rw [P.sum_idempotent_projectiveCategory]
        simp only [mul_one]
    _ = (∑ X : S.ProjectiveCategory,
          P.idempotent (S.projectiveCategoryLabel X)) * a := by
        rw [Finset.sum_mul]
    _ = a := by
        rw [P.sum_idempotent_projectiveCategory, one_mul]

private theorem fromSmallBasicAlgebra_toSmallBasicAlgebra
    (a : Aᵐᵒᵖ) :
    P.fromSmallBasicAlgebra (P.toSmallBasicAlgebraAlgHom a) = a := by
  apply MulOpposite.unop_injective
  change (∑ X : S.ProjectiveCategory,
      ∑ Y : S.ProjectiveCategory,
        P.matrixCoordinate (P.smallComponentMatrix a.unop) X Y) = a.unop
  simp_rw [matrixCoordinate_smallComponentMatrix]
  exact P.sum_all_corners a.unop

private theorem idempotent_mul_matrixCoordinate
    [DecidableEq S.ProjectiveCategory]
    (f : smallBasicAlgebra (k := k) (S := S))
    (X U V : S.ProjectiveCategory) :
    P.idempotent (S.projectiveCategoryLabel X) *
        P.matrixCoordinate f U V =
      if X = U then P.matrixCoordinate f U V else 0 := by
  classical
  by_cases hXU : X = U
  · subst U
    rw [if_pos rfl]
    exact P.idempotent_mul_projectiveHomCoordinate
      (componentPreimage f X V)
  · rw [if_neg hXU]
    change P.idempotent (S.projectiveCategoryLabel X) *
      P.projectiveHomCoordinate (componentPreimage f U V) = 0
    rw [← P.idempotent_mul_projectiveHomCoordinate
      (p := S.projectiveCategoryLabel V)
      (q := S.projectiveCategoryLabel U)
      (componentPreimage f U V)]
    rw [← mul_assoc, P.complete.ortho
      (fun h ↦ hXU (S.projectiveCategoryLabel_injective h)), zero_mul]

private theorem matrixCoordinate_mul_idempotent
    [DecidableEq S.ProjectiveCategory]
    (f : smallBasicAlgebra (k := k) (S := S))
    (U V Y : S.ProjectiveCategory) :
    P.matrixCoordinate f U V *
        P.idempotent (S.projectiveCategoryLabel Y) =
      if V = Y then P.matrixCoordinate f U V else 0 := by
  classical
  by_cases hVY : V = Y
  · subst Y
    rw [if_pos rfl]
    exact P.projectiveHomCoordinate_mul_idempotent
      (componentPreimage f U V)
  · rw [if_neg hVY]
    change P.projectiveHomCoordinate (componentPreimage f U V) *
      P.idempotent (S.projectiveCategoryLabel Y) = 0
    rw [← P.projectiveHomCoordinate_mul_idempotent
      (p := S.projectiveCategoryLabel V)
      (q := S.projectiveCategoryLabel U)
      (componentPreimage f U V)]
    rw [mul_assoc, P.complete.ortho
      (fun h ↦ hVY (S.projectiveCategoryLabel_injective h)), mul_zero]

/-- Complete orthogonal idempotents isolate the original matrix component
from the sum of all recovered coordinates. -/
private theorem corner_fromSmallBasicAlgebra
    (f : smallBasicAlgebra (k := k) (S := S))
    (X Y : S.ProjectiveCategory) :
    P.idempotent (S.projectiveCategoryLabel X) *
        (P.fromSmallBasicAlgebra f).unop *
          P.idempotent (S.projectiveCategoryLabel Y) =
      P.matrixCoordinate f X Y := by
  classical
  change P.idempotent (S.projectiveCategoryLabel X) *
      (∑ U : S.ProjectiveCategory,
        ∑ V : S.ProjectiveCategory, P.matrixCoordinate f U V) *
        P.idempotent (S.projectiveCategoryLabel Y) = _
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, P.idempotent_mul_matrixCoordinate]
  rw [Fintype.sum_eq_single X]
  · simp only [if_pos]
    rw [Finset.sum_mul]
    simp_rw [P.matrixCoordinate_mul_idempotent]
    rw [Fintype.sum_ite_eq' Y]
  · intro U hUX
    simp only [if_neg (Ne.symm hUX), Finset.sum_const_zero]

private theorem toSmallBasicAlgebra_fromSmallBasicAlgebra
    (f : smallBasicAlgebra (k := k) (S := S)) :
    P.toSmallBasicAlgebraAlgHom (P.fromSmallBasicAlgebra f) = f := by
  apply (biproduct.matrixEquiv).injective
  funext X Y
  change biproduct.components
      (P.smallComponentMatrix (P.fromSmallBasicAlgebra f).unop) X Y =
    biproduct.components f X Y
  rw [smallComponentMatrix_components]
  have hcomponent :
      P.projectiveComponent (P.fromSmallBasicAlgebra f).unop X Y =
        componentPreimage f X Y := by
    apply P.projectiveHomCoordinate_injective
      (S.projectiveCategoryLabel Y) (S.projectiveCategoryLabel X)
    change P.projectiveHomCoordinate
        (P.projectiveComponent (P.fromSmallBasicAlgebra f).unop X Y) =
      P.projectiveHomCoordinate (componentPreimage f X Y)
    rw [projectiveHomCoordinate_projectiveComponent,
      P.corner_fromSmallBasicAlgebra]
    rfl
  rw [hcomponent]
  simp only [componentPreimage]
  rw [Quiver.Hom.op_unop, (F (k := k) (S := S)).map_preimage]

/-- The small selected-projective category algebra is the opposite ambient
algebra. -/
private def smallBasicAlgebraAlgEquiv :
    Aᵐᵒᵖ ≃ₐ[k] smallBasicAlgebra (k := k) (S := S) :=
  AlgEquiv.ofBijective P.toSmallBasicAlgebraAlgHom
    ⟨(Function.LeftInverse.injective
        P.fromSmallBasicAlgebra_toSmallBasicAlgebra),
      fun f ↦ ⟨P.fromSmallBasicAlgebra f,
        P.toSmallBasicAlgebra_fromSmallBasicAlgebra f⟩⟩

/-- The category algebra used by the lifted ordinary-quiver presentation is
canonically the opposite of the ambient right-module algebra. -/
noncomputable def basicAlgebraAlgEquiv : Aᵐᵒᵖ ≃ₐ[k] S.basicAlgebra :=
  P.smallBasicAlgebraAlgEquiv.trans S.projectiveCategoryAlgebraEquiv

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
