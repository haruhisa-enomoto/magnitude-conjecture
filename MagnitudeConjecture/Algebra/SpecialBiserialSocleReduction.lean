import MagnitudeConjecture.Algebra.SpecialBiserialStringProjectiveInjective
import MagnitudeConjecture.Algebra.RightModuleSocleFamilyPresentationIndependence
import MagnitudeConjecture.Algebra.RightModuleSocleFamilyAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModuleCanonicalSocleFamilyAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModuleSocleReductionString
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators

/-!
# Socle reduction of representation-finite special-biserial algebras

For a special-biserial bound-quiver presentation, the kernel of the canonical
map to its path-support-hull string algebra is exactly the simultaneous socle
ideal of the nonuniserial indecomposable projective-injective modules.  The
final theorem transports this equality across the literal presentation and
primitive-projective presentation chosen by the caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule

universe u

variable {A : Type u} [Ring A]

/-- The part of a two-sided ideal lying in a principal right ideal. -/
def idealRightIdealSubmodule (I : TwoSidedIdeal A) (e : A) :
    Submodule Aᵐᵒᵖ (rightIdeal e) where
  carrier := {x | x.1 ∈ I}
  zero_mem' := I.zero_mem
  add_mem' hx hy := I.add_mem hx hy
  smul_mem' r x hx := by
    change x.1 * r.unop ∈ I
    exact I.mul_mem_right _ _ hx

@[simp]
theorem mem_idealRightIdealSubmodule
    (I : TwoSidedIdeal A) (e : A) (x : rightIdeal e) :
    x ∈ idealRightIdealSubmodule I e ↔ x.1 ∈ I :=
  Iff.rfl

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator

universe u

variable {k C : Type u} [Field k]
variable [Category.{u} C] [Preadditive C] [Linear k C] [Fintype C]
variable (hC : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))

private abbrev largeRepresentable (X : C) :=
  (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
    (Opposite.op X)

local instance largeAlgebraFiniteDimensional :
    FiniteDimensional k (algebra hC) :=
  algebra_finiteDimensional hC

local instance largeAlgebraOppositeIsNoetherian :
    IsNoetherianRing (algebra hC)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

theorem smallCanonicalProjector_complete :
    CompleteOrthogonalIdempotents
      (smallCanonicalProjector hC) := by
  let e := Fintype.equivFin C
  let R := fun X : C ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
      (Opposite.op X)
  let Rs := fun i : SmallIndex (C := C) ↦ R (e.symm i)
  refine {
    idem := ?_
    ortho := ?_
    complete := ?_ }
  · intro i
    rw [IsIdempotentElem, End.mul_def]
    simp [smallCanonicalProjector, R, Category.assoc]
  · intro i j hij
    change smallCanonicalProjector hC i *
      smallCanonicalProjector hC j = 0
    rw [End.mul_def]
    simp only [smallCanonicalProjector, Category.assoc]
    have hobj : e.symm j ≠ e.symm i := by
      intro h
      exact hij (e.symm.injective h.symm)
    rw [← Category.assoc
      (biproduct.ι R (e.symm j))
      (biproduct.π R (e.symm i)),
      biproduct.ι_π_ne _ hobj, zero_comp, comp_zero]
  · change (∑ i : SmallIndex (C := C),
        smallCanonicalProjector hC i) = 𝟙 _
    calc
      _ = ∑ i : SmallIndex (C := C),
          (generatorSmallIso hC).hom ≫
            (biproduct.π Rs i ≫ biproduct.ι Rs i) ≫
            (generatorSmallIso hC).inv := by
        apply Finset.sum_congr rfl
        intro i _
        exact smallCanonicalProjector_eq_conjugate hC i
      _ = (generatorSmallIso hC).hom ≫
          (∑ i : SmallIndex (C := C),
            biproduct.π Rs i ≫ biproduct.ι Rs i) ≫
          (generatorSmallIso hC).inv := by
        rw [← Preadditive.comp_sum, ← Preadditive.sum_comp]
      _ = 𝟙 _ := by
        rw [biproduct.total]
        rw [Category.id_comp]
        exact (generatorSmallIso hC).hom_inv_id

theorem smallCanonicalProjector_primitive
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (i : SmallIndex (C := C)) :
    MagnitudeConjecture.RightModule.PrimitiveIdempotentData
      (smallCanonicalProjector hC i) := by
  let X := (Fintype.equivFin C).symm i
  letI : IsLocalRing (End (largeRepresentable hC X)) :=
    finiteDimensionalLinearCoyoneda_end_isLocalRing hC hlocal X
  exact MagnitudeConjecture.CoveringHom.biproductProjector_primitive
    (fun Y : C ↦ largeRepresentable hC Y) X
    (finiteDimensionalLinearCoyoneda_indecomposable hC hlocal X).1

def smallCanonicalRightIdealLinearEquiv
    (i : SmallIndex (C := C)) :
    MagnitudeConjecture.RightModule.rightIdealFGObj
        (smallCanonicalProjector hC i) ≃ₗ[(algebra hC)ᵐᵒᵖ]
      (representedFGFunctor hC).obj
        (largeRepresentable hC ((Fintype.equivFin C).symm i)) where
  toFun q := q.1 ≫ biproduct.π (largeRepresentable hC)
    ((Fintype.equivFin C).symm i)
  invFun f := ⟨f ≫ biproduct.ι (largeRepresentable hC)
      ((Fintype.equivFin C).symm i), ⟨
    f ≫ biproduct.ι (largeRepresentable hC)
      ((Fintype.equivFin C).symm i), by
      change (f ≫ biproduct.ι (largeRepresentable hC)
          ((Fintype.equivFin C).symm i)) ≫
          smallCanonicalProjector hC i =
        f ≫ biproduct.ι (largeRepresentable hC)
          ((Fintype.equivFin C).symm i)
      simp [smallCanonicalProjector, Category.assoc]⟩⟩
  map_add' q r := by
    change (q.1 + r.1) ≫ biproduct.π (largeRepresentable hC)
        ((Fintype.equivFin C).symm i) = _
    exact Preadditive.add_comp _ _ _ _ _ _
  map_smul' a q := by
    change a.unop ≫ q.1 ≫ biproduct.π (largeRepresentable hC)
        ((Fintype.equivFin C).symm i) =
      a.unop ≫ (q.1 ≫ biproduct.π (largeRepresentable hC)
        ((Fintype.equivFin C).symm i))
    rfl
  left_inv q := by
    apply Subtype.ext
    change q.1 ≫ smallCanonicalProjector hC i = q.1
    have hfixed := MagnitudeConjecture.RightModule.rightIdeal_fixed
      ((smallCanonicalProjector_complete hC).idem i) q
    change q.1 ≫ smallCanonicalProjector hC i = q.1 at hfixed
    exact hfixed
  right_inv f := by
    change (f ≫ biproduct.ι (largeRepresentable hC)
        ((Fintype.equivFin C).symm i)) ≫
        biproduct.π (largeRepresentable hC)
          ((Fintype.equivFin C).symm i) = f
    simp

def smallCanonicalRightIdealIso (i : SmallIndex (C := C)) :
    MagnitudeConjecture.RightModule.rightIdealFGObj
        (smallCanonicalProjector hC i) ≅
      (representedFGFunctor hC).obj
        (largeRepresentable hC ((Fintype.equivFin C).symm i)) :=
  QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
    (algebra hC)ᵐᵒᵖ (smallCanonicalRightIdealLinearEquiv hC i)

variable (hlocal : ∀ X : C, IsLocalRing (End X))
variable (S : MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
  k (algebra hC))

def smallCanonicalSourceLabel
    (i : SmallIndex (C := C)) : S.ProjectiveLabel :=
  S.primitiveSourceProjectiveLabel
    (smallCanonicalProjector_primitive hC hlocal i)

def smallCanonicalRepresentableSourceIso
    (i : SmallIndex (C := C)) :
    (representedFGFunctor hC).obj
        (largeRepresentable hC ((Fintype.equivFin C).symm i)) ≅
      S.fgObj (smallCanonicalSourceLabel hC hlocal S i).label :=
  (smallCanonicalRightIdealIso hC i).symm ≪≫
    S.primitiveSourceIso (smallCanonicalProjector_primitive hC hlocal i)

theorem smallCanonicalSourceLabel_injective (hskel : Skeletal C) :
    Function.Injective (smallCanonicalSourceLabel hC hlocal S) := by
  intro i j hij
  apply (Fintype.equivFin C).symm.injective
  apply hskel
  apply Nonempty.intro
  let eTarget :
      (representedFGFunctor hC).obj
          (largeRepresentable hC ((Fintype.equivFin C).symm i)) ≅
        (representedFGFunctor hC).obj
          (largeRepresentable hC ((Fintype.equivFin C).symm j)) :=
    (smallCanonicalRepresentableSourceIso hC hlocal S i).trans
      ((eqToIso (congrArg (fun p : S.ProjectiveLabel ↦
        S.fgObj p.label) hij)).trans
        (smallCanonicalRepresentableSourceIso hC hlocal S j).symm)
  let eRepresentable :
      largeRepresentable hC ((Fintype.equivFin C).symm i) ≅
        largeRepresentable hC ((Fintype.equivFin C).symm j) :=
    (representedFGFunctor hC).preimageIso eTarget
  let J := finiteDimensionalLinearCoyonedaFunctor (k := k) hC
  letI : J.Full := by
    dsimp [J, finiteDimensionalLinearCoyonedaFunctor,
      linearCoyonedaLinearModuleFunctor]
    infer_instance
  letI : J.Faithful := by
    dsimp [J, finiteDimensionalLinearCoyonedaFunctor,
      linearCoyonedaLinearModuleFunctor]
    infer_instance
  let eOpposite := J.preimageIso eRepresentable
  exact eOpposite.unop.symm

theorem smallCanonicalSourceLabel_surjective :
    Function.Surjective (smallCanonicalSourceLabel hC hlocal S) := by
  intro p
  let E := moduleEquivalence hC
  letI : E.functor.Additive :=
    { map_add := by
        intro X Y f g
        change (representedFGFunctor hC).map (f + g) =
          (representedFGFunctor hC).map f +
            (representedFGFunctor hC).map g
        exact (representedFGFunctor hC).map_add }
  letI : E.inverse.Additive := inferInstance
  let M := E.inverse.obj (S.fgObj p.label)
  have hMind : Indecomposable M :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse (S.fgObj p.label)).2 (S.fgObj_indecomposable p.label)
  letI : Projective M :=
    (E.symm.map_projective_iff (S.fgObj p.label)).2 p.projective
  obtain ⟨X, ⟨eX⟩⟩ :=
    indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      hC hlocal M hMind
  let i := Fintype.equivFin C X
  let eTarget :
      (representedFGFunctor hC).obj (largeRepresentable hC X) ≅
        S.fgObj p.label :=
    (E.functor.mapIso eX).trans (E.counitIso.app (S.fgObj p.label))
  have hlabel : (smallCanonicalSourceLabel hC hlocal S i).label =
      p.label :=
    S.fgObj_skeletal ⟨
      (smallCanonicalRepresentableSourceIso hC hlocal S i).symm.trans
        ((representedFGFunctor hC).mapIso (eqToIso (by
            change (largeRepresentable hC ((Fintype.equivFin C).symm i)) =
              largeRepresentable hC X
            rw [(Fintype.equivFin C).symm_apply_apply])) |>.trans eTarget)⟩
  refine ⟨i, ?_⟩
  let q := smallCanonicalSourceLabel hC hlocal S i
  have hlabel' : q.label = p.label := hlabel
  change q = p
  rcases hq : q with ⟨j, hj⟩
  rcases hp : p with ⟨l, hl⟩
  rw [hq, hp] at hlabel'
  change j = l at hlabel'
  subst l
  rfl

def smallCanonicalSourceEquiv (hskel : Skeletal C) :
    SmallIndex (C := C) ≃ S.ProjectiveLabel :=
  Equiv.ofBijective (smallCanonicalSourceLabel hC hlocal S)
    ⟨smallCanonicalSourceLabel_injective hC hlocal S hskel,
      smallCanonicalSourceLabel_surjective hC hlocal S⟩

def smallPrimitiveProjectivePresentation (hskel : Skeletal C) :
    S.PrimitiveProjectivePresentation where
  idempotent p := smallCanonicalProjector hC
    ((smallCanonicalSourceEquiv hC hlocal S hskel).symm p)
  complete :=
    (CompleteOrthogonalIdempotents.equiv
      (e := smallCanonicalProjector hC)
      (smallCanonicalSourceEquiv hC hlocal S hskel).symm).2
        (smallCanonicalProjector_complete hC)
  primitive p := smallCanonicalProjector_primitive hC hlocal
    ((smallCanonicalSourceEquiv hC hlocal S hskel).symm p)
  sourceLabel p := by
    change smallCanonicalSourceLabel hC hlocal S
      ((smallCanonicalSourceEquiv hC hlocal S hskel).symm p) = p
    exact (smallCanonicalSourceEquiv hC hlocal S hskel).apply_symm_apply p

theorem algebraCategoryCoordinate_rightIdeal_eq_zero
    {X Y Z : C}
    (q : MagnitudeConjecture.RightModule.rightIdeal
      (smallCanonicalProjector hC (Fintype.equivFin C Z))) (hYZ : Y ≠ Z) :
    algebraCategoryCoordinate hC q.1 X Y = 0 := by
  obtain ⟨a, ha⟩ := q.2
  change a ≫ smallCanonicalProjector hC (Fintype.equivFin C Z) = q.1 at ha
  have hproj : q.1 ≫ biproduct.π
      (fun W : C ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
          (Opposite.op W)) Y = 0 := by
    calc
      _ = (a ≫ smallCanonicalProjector hC (Fintype.equivFin C Z)) ≫
          biproduct.π
            (fun W : C ↦
              (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
                (Opposite.op W)) Y := by rw [ha]
      _ = 0 := by
        have hCP : smallCanonicalProjector hC (Fintype.equivFin C Z) =
            biproduct.π
                (fun W : C ↦
                  (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
                    (Opposite.op W)) Z ≫
              biproduct.ι
                (fun W : C ↦
                  (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
                    (Opposite.op W)) Z := by
          unfold smallCanonicalProjector
          rw [(Fintype.equivFin C).symm_apply_apply]
        rw [hCP]
        simp only [Category.assoc]
        rw [biproduct.ι_π_ne _ (Ne.symm hYZ), comp_zero, comp_zero]
  have hmatrix :
      biproduct.ι
          (fun W : C ↦
            (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
              (Opposite.op W)) X ≫ q.1 ≫
        biproduct.π
          (fun W : C ↦
            (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
              (Opposite.op W)) Y = 0 := by
    rw [hproj, comp_zero]
  unfold algebraCategoryCoordinate
  rw [hmatrix]
  simp
  rfl

theorem exists_algebraCategoryCoordinate_ne_zero_of_rightIdeal
    {Z : C}
    (q : MagnitudeConjecture.RightModule.rightIdeal
      (smallCanonicalProjector hC (Fintype.equivFin C Z))) (hq : q ≠ 0) :
    ∃ X : C, algebraCategoryCoordinate hC q.1 X Z ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hq
  apply Subtype.ext
  apply algebraCategoryCoordinate_ext hC
  intro X Y
  have hzero : algebraCategoryCoordinate hC (0 : algebra hC) X Y = 0 := by
    unfold algebraCategoryCoordinate
    simp
    rfl
  by_cases hYZ : Y = Z
  · subst Y
    change algebraCategoryCoordinate hC q.1 X Z =
      algebraCategoryCoordinate hC (0 : algebra hC) X Z
    rw [hzero]
    exact hall X
  · rw [algebraCategoryCoordinate_rightIdeal_eq_zero hC q hYZ]
    change 0 = algebraCategoryCoordinate hC (0 : algebra hC) X Y
    exact hzero.symm

theorem algebraCategoryCoordinate_smul
    (c : k) (a : algebra hC) (X Y : C) :
    algebraCategoryCoordinate hC (c • a) X Y =
      c • algebraCategoryCoordinate hC a X Y := by
  have hs := smallAlgebraCategoryCoordinate_smul hC c a
    (Fintype.equivFin C X) (Fintype.equivFin C Y)
  rw [smallAlgebraCategoryCoordinate_eq_algebraCategoryCoordinate,
    smallAlgebraCategoryCoordinate_eq_algebraCategoryCoordinate] at hs
  rw [(Fintype.equivFin C).symm_apply_apply X,
    (Fintype.equivFin C).symm_apply_apply Y] at hs
  exact hs

end MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator

namespace MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

theorem exists_surviving_hullKilledPath_of_relative_ne_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (f : obj P.toPresentation.relations z ⟶
      obj P.toPresentation.relations x)
    (hf : f ∈ (relativeRelationHomIdeal
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)).hom
          (obj P.toPresentation.relations z)
          (obj P.toPresentation.relations x))
    (hfne : f ≠ 0) :
    ∃ s : Quiver.Path x z,
      pathMap P.toPresentation.relations s ≠ 0 ∧
        pathMap (pathSupportHull P.toPresentation.relations) s = 0 := by
  let T := {s : Quiver.Path x z //
    pathMap (pathSupportHull P.toPresentation.relations) s = 0}
  have hfspan : f ∈ Submodule.span k
      (Set.range fun s : T ↦ pathMap P.toPresentation.relations s.1) := by
    rw [← relativeRelationHomIdeal_eq_span_killedPathMap
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)
      (pathSupportHull_isMonomial P.toPresentation.relations) x z]
    exact hf
  by_contra hex
  push Not at hex
  have hspan : Submodule.span k
      (Set.range fun s : T ↦ pathMap P.toPresentation.relations s.1) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro g ⟨s, rfl⟩
    by_contra hs
    exact hex s.1 hs s.2
  rw [hspan] at hfspan
  exact hfne hfspan

theorem exists_relationSurvivingSupport_of_surviving_hullKilledPath
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q} (s : Quiver.Path x z)
    (hsSurvives : pathMap P.toPresentation.relations s ≠ 0)
    (hsHull : pathMap (pathSupportHull P.toPresentation.relations) s = 0) :
    ∃ (r : LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q x),
      r ∈ P.toPresentation.relations
          (LinearPathCategory.obj k Q z)
          (LinearPathCategory.obj k Q x) ∧
        Nonempty (P.RelationSurvivingSupport r) := by
  obtain ⟨U, V, q, hqHull, a, b, hs⟩ :=
    exists_relation_path_factor_of_pathMap_eq_zero
      (pathSupportHull_isPathRelationFamily P.toPresentation.relations)
      s hsHull
  have hqSurvives : pathMap P.toPresentation.relations q ≠ 0 := by
    intro hqZero
    apply hsSurvives
    rw [hs, ← pathMap_comp, ← pathMap_comp]
    rw [hqZero]
    simp
  have haLength : a.length = 0 := by
    by_contra ha
    have hzero := P.pathMap_comp_pathSupportHullGenerator_eq_zero
      hqHull a ha
    change pathMap P.toPresentation.relations a ≫
      pathMap P.toPresentation.relations q = 0 at hzero
    apply hsSurvives
    rw [hs, ← pathMap_comp, ← pathMap_comp]
    rw [← Category.assoc, hzero, CategoryTheory.Limits.zero_comp]
  have hbLength : b.length = 0 := by
    by_contra hb
    have hzero := P.pathSupportHullGenerator_comp_pathMap_eq_zero
      hqHull b hb
    change pathMap P.toPresentation.relations q ≫
      pathMap P.toPresentation.relations b = 0 at hzero
    apply hsSurvives
    rw [hs, ← pathMap_comp, ← pathMap_comp]
    rw [hzero, CategoryTheory.Limits.comp_zero]
  rcases hqHull with ⟨q', hqq', r, hr, hcoeff⟩
  have hqq : q = q' := by
    apply (LinearPathCategory.homPathBasis U V).injective
    simpa only [LinearPathCategory.homPathBasis_apply] using hqq'
  subst q'
  have hU : LinearPathCategory.vertex U = z :=
    a.eq_of_length_zero haLength
  have hV : x = LinearPathCategory.vertex V :=
    b.eq_of_length_zero hbLength
  dsimp only [LinearPathCategory.vertex] at hU hV
  subst U
  subst V
  refine ⟨r, hr, ⟨⟨q, hcoeff, hqSurvives⟩⟩⟩

private abbrev quotientCategoryAlgebra
    (P : SpecialBiserialPresentation k A Q) :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra
    (finiteRepresentablesOfAdmissible.{u, u, u}
      P.toPresentation.admissible)

private abbrev quotientCategoryRepresentables
    (P : SpecialBiserialPresentation k A Q) :=
  finiteRepresentablesOfAdmissible.{u, u, u}
    P.toPresentation.admissible

local instance quotientCategoryAlgebraFiniteDimensional
    (P : SpecialBiserialPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    P.quotientCategoryRepresentables

local instance quotientCategoryAlgebraOppositeIsNoetherian
    (P : SpecialBiserialPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

def relativeHullAlgebraHom (P : SpecialBiserialPresentation k A Q) :
    P.quotientCategoryAlgebra →ₐ[k]
      CoveringHom.finiteCategoryProjectiveGenerator.algebra
        (finiteRepresentablesOfAdmissible.{u, u, u}
          (pathSupportHull_isAdmissible P.toPresentation.admissible)) :=
  relationQuotientAlgebraHom
    P.toPresentation.admissible
    (pathSupportHull_isAdmissible P.toPresentation.admissible)
    (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
      P.toPresentation.relations)

def relativeHullKernelRow
    (P : SpecialBiserialPresentation k A Q) (z : Q) :
    Submodule P.quotientCategoryAlgebraᵐᵒᵖ
      (RightModule.rightIdeal
        (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
          P.quotientCategoryRepresentables
          (Fintype.equivFin
            (Category.{u, u, u} P.toPresentation.relations)
            (obj P.toPresentation.relations z)))) :=
  RightModule.idealRightIdealSubmodule
    (TwoSidedIdeal.ker P.relativeHullAlgebraHom)
    (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
      P.quotientCategoryRepresentables
      (Fintype.equivFin
        (Category.{u, u, u} P.toPresentation.relations)
        (obj P.toPresentation.relations z)))

theorem relativeHullKernelRow_coordinate_mem
    (P : SpecialBiserialPresentation k A Q) (z : Q)
    (q : P.relativeHullKernelRow z)
    (X Y : Category.{u, u, u} P.toPresentation.relations) :
    CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
        P.quotientCategoryRepresentables q.1.1 X Y ∈
      (relativeRelationHomIdeal
        (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
          P.toPresentation.relations)).hom Y X := by
  rw [mem_relativeRelationHomIdeal_iff]
  apply (relationQuotientAlgebraHom_eq_zero_iff_objectCoordinate
    P.toPresentation.admissible
    (pathSupportHull_isAdmissible P.toPresentation.admissible)
    (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
      P.toPresentation.relations) q.1.1).1
  have hq := q.property
  change q.1.1 ∈ TwoSidedIdeal.ker P.relativeHullAlgebraHom at hq
  exact (TwoSidedIdeal.mem_ker P.relativeHullAlgebraHom).1 hq

theorem exists_relationSurvivingSupport_of_relativeHullKernelRow_ne_zero
    (P : SpecialBiserialPresentation k A Q) (z : Q)
    (q : P.relativeHullKernelRow z) (hq : q ≠ 0) :
    ∃ (x : Q)
      (r : LinearPathCategory.obj k Q z ⟶ LinearPathCategory.obj k Q x)
      (hr : r ∈ P.relations
        (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q x)),
      Nonempty (P.RelationSurvivingSupport r) := by
  classical
  let hP := P.quotientCategoryRepresentables
  let R := P.relations
  have hqRightIdeal : q.1 ≠ 0 := by
    intro hzero
    apply hq
    exact Subtype.ext hzero
  obtain ⟨X, hXne⟩ :=
    CoveringHom.finiteCategoryProjectiveGenerator.exists_algebraCategoryCoordinate_ne_zero_of_rightIdeal
      hP q.1 hqRightIdeal
  let e : Category R ≃ Q := relationQuotientObjectEquiv R
  let x := e X
  have hX : obj R x = X := e.symm_apply_apply X
  have hfne :
      CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
        hP q.1.1 (obj R x) (obj R z) ≠ 0 := by
    rw [hX]
    exact hXne
  have hfmem := P.relativeHullKernelRow_coordinate_mem z q
    (obj R x) (obj R z)
  obtain ⟨s, hsSurvives, hsHull⟩ :=
    P.exists_surviving_hullKilledPath_of_relative_ne_zero
      (CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
        hP q.1.1 (obj R x) (obj R z)) hfmem hfne
  obtain ⟨r, hr, hp⟩ :=
    P.exists_relationSurvivingSupport_of_surviving_hullKilledPath
      s hsSurvives hsHull
  exact ⟨x, r, hr, hp⟩

theorem relativeHullKernelRow_eq_smul_of_ne_zero
    (P : SpecialBiserialPresentation k A Q) (z : Q)
    (q₀ : P.relativeHullKernelRow z) (hq₀ : q₀ ≠ 0)
    (q : P.relativeHullKernelRow z) :
    ∃ c : k, q = c • q₀ := by
  classical
  let hP := P.quotientCategoryRepresentables
  let R := P.toPresentation.relations
  let C := Category.{u, u, u} R
  have hq₀RightIdeal : q₀.1 ≠ 0 := by
    intro h
    apply hq₀
    apply Subtype.ext
    exact h
  obtain ⟨X, hXne⟩ :=
    CoveringHom.finiteCategoryProjectiveGenerator.exists_algebraCategoryCoordinate_ne_zero_of_rightIdeal
      hP q₀.1 hq₀RightIdeal
  let e := relationQuotientObjectEquiv R
  let x := e X
  have hX : obj R x = X := e.symm_apply_apply X
  have hf₀ne :
      CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
        hP q₀.1.1 (obj R x) (obj R z) ≠ 0 := by
    rw [hX]
    exact hXne
  have hf₀mem := P.relativeHullKernelRow_coordinate_mem z q₀
    (obj R x) (obj R z)
  obtain ⟨s, hsSurvives, hsHull⟩ :=
    P.exists_surviving_hullKilledPath_of_relative_ne_zero
      (CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
        hP q₀.1.1 (obj R x) (obj R z)) hf₀mem hf₀ne
  obtain ⟨r, hr, ⟨p⟩⟩ :=
    P.exists_relationSurvivingSupport_of_surviving_hullKilledPath
      s hsSurvives hsHull
  let v := pathMap R p.1
  let f₀ :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
      hP q₀.1.1 (obj R x) (obj R z)
  have hf₀span : f₀ ∈ Submodule.span k {v} := by
    rw [← P.relativePathSupportHull_endpoint_eq_span_singleton r hr p]
    exact hf₀mem
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hf₀span
  have hdne : d ≠ 0 := by
    intro hdzero
    apply hf₀ne
    change f₀ = 0
    rw [← hd, hdzero, zero_smul]
  let f :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
      hP q.1.1 (obj R x) (obj R z)
  have hfmem := P.relativeHullKernelRow_coordinate_mem z q
    (obj R x) (obj R z)
  have hfspan : f ∈ Submodule.span k {v} := by
    rw [← P.relativePathSupportHull_endpoint_eq_span_singleton r hr p]
    exact hfmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfspan
  let t := c * d⁻¹
  have hendpoint : f = t • f₀ := by
    calc
      f = c • v := hc.symm
      _ = t • (d • v) := by
        rw [smul_smul]
        change c • v = (c * d⁻¹ * d) • v
        rw [mul_assoc, inv_mul_cancel₀ hdne, mul_one]
      _ = t • f₀ := by rw [hd]
  have halg : q.1.1 = t • q₀.1.1 := by
    apply CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate_ext
      hP
    intro U V
    by_cases hVz : V = obj R z
    · subst V
      rw [CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate_smul]
      by_cases hUx : U = obj R x
      · subst U
        exact hendpoint
      · let y := e U
        have hU : obj R y = U := e.symm_apply_apply U
        have hyx : y ≠ x := by
          intro hyx
          apply hUx
          rw [← hU, hyx]
        rw [← hU]
        have hqmem := P.relativeHullKernelRow_coordinate_mem z q
            (obj R y) (obj R z)
        have hq₀mem := P.relativeHullKernelRow_coordinate_mem z q₀
            (obj R y) (obj R z)
        have hbot := P.relativePathSupportHull_terminalCoordinate_eq_bot_of_ne
          r hr p hyx
        change
          CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
              hP q.1.1 (obj R y) (obj R z) ∈
            CategoricalIdeal.HomIdeal.homSubmodule (k := k)
              (relativeRelationHomIdeal
                (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal P.relations))
              (obj R z) (obj R y) at hqmem
        change
          CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
              hP q₀.1.1 (obj R y) (obj R z) ∈
            CategoricalIdeal.HomIdeal.homSubmodule (k := k)
              (relativeRelationHomIdeal
                (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal P.relations))
              (obj R z) (obj R y) at hq₀mem
        rw [hbot] at hqmem hq₀mem
        have hqzero :
            CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
              hP q.1.1 (obj R y) (obj R z) = 0 := by
          simpa using hqmem
        have hq₀zero :
            CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
              hP q₀.1.1 (obj R y) (obj R z) = 0 := by
          simpa using hq₀mem
        rw [hqzero, hq₀zero, smul_zero]
    · rw [
        CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate_rightIdeal_eq_zero
          hP q.1 hVz,
        CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate_smul,
        CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate_rightIdeal_eq_zero
          hP q₀.1 hVz,
        smul_zero]
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact halg

theorem relativeHullKernelRow_isSimple_of_ne_zero
    (P : SpecialBiserialPresentation k A Q) (z : Q)
    (q₀ : P.relativeHullKernelRow z) (hq₀ : q₀ ≠ 0) :
    IsSimpleModule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.relativeHullKernelRow z) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨⟨q₀, 0, hq₀⟩⟩, ?_⟩
  intro q hq q'
  obtain ⟨c, hc⟩ := P.relativeHullKernelRow_eq_smul_of_ne_zero z q hq q'
  refine ⟨algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ c, ?_⟩
  calc
    (algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ c) • q = c • q := by
      apply Subtype.ext
      apply Subtype.ext
      change q.1.1 * (algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ c).unop =
        c • q.1.1
      rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op,
        Algebra.smul_def, Algebra.commutes]
    _ = q' := hc.symm

theorem relativeHullKernelRow_le_moduleSocle_of_ne_bot
    (P : SpecialBiserialPresentation k A Q) (z : Q)
    (hrow : P.relativeHullKernelRow z ≠ ⊥) :
    P.relativeHullKernelRow z ≤
      moduleSocle P.quotientCategoryAlgebraᵐᵒᵖ
        (RightModule.rightIdeal
          (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
            P.quotientCategoryRepresentables
            (Fintype.equivFin
              (Category.{u, u, u} P.relations) (obj P.relations z)))) := by
  letI : Nontrivial (P.relativeHullKernelRow z) :=
    Submodule.nontrivial_iff_ne_bot.mpr hrow
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : P.relativeHullKernelRow z)
  exact le_moduleSocle_of_simple (P.relativeHullKernelRow z)
    (P.relativeHullKernelRow_isSimple_of_ne_zero z q₀ hq₀)

def quotientVertexProjectiveLabel
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (z : Q) : S.ProjectiveLabel :=
  CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalSourceLabel
    P.quotientCategoryRepresentables
    (fun X ↦ P.toPresentation.admissible.quotientEnd_isLocalRing X)
    S
    (Fintype.equivFin (Category.{u, u, u} P.relations)
      (obj P.relations z))

def quotientCategoryPrimitiveProjectivePresentation
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    S.PrimitiveProjectivePresentation := by
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
      P.quotientCategoryRepresentables
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.smallPrimitiveProjectivePresentation
      P.quotientCategoryRepresentables
      (fun X ↦ P.toPresentation.admissible.quotientEnd_isLocalRing X)
      S P.toPresentation.admissible.quotientCategory_skeletal

theorem quotientCategoryPrimitiveProjectivePresentation_idempotent_vertex
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (z : Q) :
    (P.quotientCategoryPrimitiveProjectivePresentation S).idempotent
        (P.quotientVertexProjectiveLabel S z) =
      CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
        P.quotientCategoryRepresentables
        (Fintype.equivFin (Category.{u, u, u} P.relations)
          (obj P.relations z)) := by
  simp [quotientCategoryPrimitiveProjectivePresentation,
    CoveringHom.finiteCategoryProjectiveGenerator.smallPrimitiveProjectivePresentation,
    quotientVertexProjectiveLabel,
    CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalSourceEquiv]

def quotientVertexProjectiveIso
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (z : Q) :
    (CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor
      P.quotientCategoryRepresentables).obj
        ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor
          P.quotientCategoryRepresentables).obj
            (Opposite.op (obj P.relations z))) ≅
      S.fgObj (P.quotientVertexProjectiveLabel S z).label := by
  simpa [quotientVertexProjectiveLabel] using
    (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalRepresentableSourceIso
      P.quotientCategoryRepresentables
      (fun X ↦ P.toPresentation.admissible.quotientEnd_isLocalRing X)
      S
      (Fintype.equivFin (Category.{u, u, u} P.relations)
        (obj P.relations z)))

theorem quotientVertexProjectiveLabel_mem_nonuniserialProjectiveInjectiveLabels
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶ LinearPathCategory.obj k Q x)
    (hr : r ∈ P.relations
      (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    P.quotientVertexProjectiveLabel S z ∈
      S.nonuniserialProjectiveInjectiveLabels := by
  let hP := P.quotientCategoryRepresentables
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let E := CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence hP
  let N :=
    (CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor hP).obj
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor hP).obj
        (Opposite.op (obj P.relations z)))
  let e := P.quotientVertexProjectiveIso S z
  have hSourceInjective : Injective
      (P.relationSourceRepresentable z) :=
    P.relationSourceRepresentable_injective r hr p
  have hNInjective : Injective N := by
    exact (E.map_injective_iff (P.relationSourceRepresentable z)).2
      hSourceInjective
  have hTargetInjective :
      Injective (S.fgObj (P.quotientVertexProjectiveLabel S z).label) :=
    Injective.of_iso e hNInjective
  have hNNotUniserial :
      ¬ IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ N :=
    P.relationSourceRepresentedModule_not_uniserial r hr p
  have hTargetNotUniserial :
      ¬ IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
        (S.fgObj (P.quotientVertexProjectiveLabel S z).label) := by
    intro hTarget
    apply hNNotUniserial
    exact IsUniserialModule.congr
      (FGModuleCat.isoToLinearEquiv e.symm) hTarget
  exact (S.mem_nonuniserialProjectiveInjectiveLabels_iff
    (P.quotientVertexProjectiveLabel S z)).2
      ⟨hTargetInjective, hTargetNotUniserial⟩

theorem relativeHullKernelRow_val_mem_socleFamily_of_ne_bot
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (z : Q)
    (hrow : P.relativeHullKernelRow z ≠ ⊥)
    (q : P.relativeHullKernelRow z) :
    q.1.1 ∈
      (P.quotientCategoryPrimitiveProjectivePresentation S
        ).primitiveProjectiveSocleFamilyIdeal
          S.nonuniserialProjectiveInjectiveLabels
          S.nonuniserialProjectiveInjectiveLabels_injective := by
  let PP := P.quotientCategoryPrimitiveProjectivePresentation S
  let pz := P.quotientVertexProjectiveLabel S z
  let T := S.nonuniserialProjectiveInjectiveLabels
  let hInjective := S.nonuniserialProjectiveInjectiveLabels_injective
  letI : Nontrivial (P.relativeHullKernelRow z) :=
    Submodule.nontrivial_iff_ne_bot.mpr hrow
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : P.relativeHullKernelRow z)
  obtain ⟨x, r, hr, ⟨p⟩⟩ :=
    P.exists_relationSurvivingSupport_of_relativeHullKernelRow_ne_zero
      z q₀ hq₀
  have hpz : pz ∈ T :=
    P.quotientVertexProjectiveLabel_mem_nonuniserialProjectiveInjectiveLabels
      S r hr p
  apply (PP.primitiveProjectiveSocleIdeal_le_familyIdeal
    T hInjective pz hpz)
  rw [PP.mem_primitiveProjectiveSocleIdeal]
  change q.1.1 ∈ PP.primitiveProjectiveSocleSubmodule pz
  rw [RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation.primitiveProjectiveSocleSubmodule]
  rw [show PP.idempotent pz =
      CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
        P.quotientCategoryRepresentables
        (Fintype.equivFin (Category.{u, u, u} P.relations)
          (obj P.relations z)) by
    exact P.quotientCategoryPrimitiveProjectivePresentation_idempotent_vertex
      S z]
  exact ⟨q.1,
    P.relativeHullKernelRow_le_moduleSocle_of_ne_bot z hrow q.property, rfl⟩

theorem relativeHullKernel_le_socleFamily
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    TwoSidedIdeal.ker P.relativeHullAlgebraHom ≤
      (P.quotientCategoryPrimitiveProjectivePresentation S
        ).primitiveProjectiveSocleFamilyIdeal
          S.nonuniserialProjectiveInjectiveLabels
          S.nonuniserialProjectiveInjectiveLabels_injective := by
  classical
  let hP := P.quotientCategoryRepresentables
  let C := Category.{u, u, u} P.relations
  let e : Q ≃ CoveringHom.finiteCategoryProjectiveGenerator.SmallIndex
      (C := C) :=
    (relationQuotientObjectEquiv P.relations).symm.trans (Fintype.equivFin C)
  let projector (z : Q) :=
    CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
      hP (e z)
  let J :=
    (P.quotientCategoryPrimitiveProjectivePresentation S
      ).primitiveProjectiveSocleFamilyIdeal
        S.nonuniserialProjectiveInjectiveLabels
        S.nonuniserialProjectiveInjectiveLabels_injective
  have hprojector (z : Q) : projector z =
      CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
        hP (Fintype.equivFin C (obj P.relations z)) := by
    rfl
  have hcomplete : (∑ z : Q, projector z) = 1 := by
    calc
      (∑ z : Q, projector z) =
          ∑ i : CoveringHom.finiteCategoryProjectiveGenerator.SmallIndex
            (C := C),
            CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
              hP i := by
        exact Equiv.sum_comp e
          (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
            hP)
      _ = 1 :=
        (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector_complete
          hP).complete
  intro a ha
  have hcomponent (z : Q) : projector z * a ∈ J := by
    let qz : P.relativeHullKernelRow z :=
      ⟨⟨projector z * a, ⟨a, by
          change
            CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
                hP (Fintype.equivFin C (obj P.relations z)) * a =
              projector z * a
          rw [hprojector]⟩⟩,
        (TwoSidedIdeal.ker P.relativeHullAlgebraHom).mul_mem_left
          (projector z) a ha⟩
    by_cases hrow : P.relativeHullKernelRow z = ⊥
    · have hqzBot : (qz :
          RightModule.rightIdeal
            (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
              hP (Fintype.equivFin C (obj P.relations z)))) ∈
            (⊥ : Submodule P.quotientCategoryAlgebraᵐᵒᵖ
              (RightModule.rightIdeal
                (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
                  hP (Fintype.equivFin C (obj P.relations z))))) := by
        rw [← hrow]
        exact qz.property
      have hqzZero : qz.1.1 = 0 := by simpa using hqzBot
      change qz.1.1 ∈ J
      rw [hqzZero]
      exact J.zero_mem
    · change qz.1.1 ∈ J
      exact P.relativeHullKernelRow_val_mem_socleFamily_of_ne_bot
        S z hrow qz
  rw [← one_mul a, ← hcomplete, Finset.sum_mul]
  exact J.finsetSum_mem Finset.univ (fun z ↦ projector z * a)
    (fun z _ ↦ hcomponent z)

end MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

theorem projectiveInjectiveIndecomposable_isUniserial_of_admitsStringPresentation
    (hString : AdmitsStringPresentation k B)
    (M : RightModule.FinitelyGeneratedCategory B)
    [Projective M] [Injective M]
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Bᵐᵒᵖ M) :
    IsUniserialModule Bᵐᵒᵖ M := by
  obtain ⟨model⟩ := hString
  letI : Fintype model.Vertex := model.vertexFintype
  letI : Quiver.{u} model.Vertex := model.quiver
  letI (x y : model.Vertex) : Fintype (x ⟶ y) :=
    model.arrowFintype x y
  let P := model.presentation
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let CAlg := P.quotientCategoryAlgebra
  letI : FiniteDimensional k CAlg :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing CAlgᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let f : B ≃ₐ[k] CAlg := P.toPresentation.algebraEquiv
  let E := RightModule.fgModuleEquivalenceOfAlgEquiv f
  let N := E.functor.obj M
  letI : Projective N := (E.map_projective_iff M).2 inferInstance
  letI : Injective N := (E.map_injective_iff M).2 inferInstance
  have hMCat : Indecomposable M :=
    (RightModule.FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := B) M).1 hM
  have hNCat : Indecomposable N :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor M).2 hMCat
  have hN : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      CAlgᵐᵒᵖ N :=
    (RightModule.FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := CAlg) N).2 hNCat
  have hNUniserial : IsUniserialModule CAlgᵐᵒᵖ N :=
    P.projectiveInjectiveIndecomposable_isUniserial N hN
  let σ := (AlgEquiv.op f).toRingEquiv
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm σ
  let e := RightModule.fgModuleMapAlgEquivSemilinearEquiv f M
  exact (isUniserialModule_iff_of_semilinearEquiv σ e).2 hNUniserial

end MagnitudeConjecture.BoundQuiver

namespace MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

local instance finalQuotientCategoryAlgebraFiniteDimensional
    (P : SpecialBiserialPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    P.quotientCategoryRepresentables

local instance finalQuotientCategoryAlgebraOppositeIsNoetherian
    (P : SpecialBiserialPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

theorem quotientVertexProjectiveLabel_surjective
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Function.Surjective (P.quotientVertexProjectiveLabel S) := by
  intro p
  let hP := P.quotientCategoryRepresentables
  let hlocal : ∀ X : Category P.relations, IsLocalRing (End X) :=
    fun X ↦ P.toPresentation.admissible.quotientEnd_isLocalRing X
  obtain ⟨i, hi⟩ :=
    CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalSourceLabel_surjective
      hP hlocal S p
  let X := (Fintype.equivFin (Category.{u, u, u} P.relations)).symm i
  let z := relationQuotientObjectEquiv P.relations X
  have hz : obj P.relations z = X :=
    (relationQuotientObjectEquiv P.relations).symm_apply_apply X
  refine ⟨z, ?_⟩
  change
    CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalSourceLabel
      hP hlocal S
        (Fintype.equivFin (Category.{u, u, u} P.relations)
          (obj P.relations z)) = p
  rw [hz, (Fintype.equivFin (Category.{u, u, u} P.relations)).apply_symm_apply]
  exact hi

theorem relativeHullQuotient_admitsStringPresentation
    (P : SpecialBiserialPresentation k A Q) :
    AdmitsStringPresentation k
      (RightModule.idealQuotientAlgebra
        (TwoSidedIdeal.ker P.relativeHullAlgebraHom)) := by
  let hHull := pathSupportHull_isAdmissible P.toPresentation.admissible
  let f := P.relativeHullAlgebraHom
  have hf : Function.Surjective f :=
    relationQuotientAlgebraHom_surjective
      P.toPresentation.admissible hHull
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)
  apply (admitsStringPresentation_iff_of_algEquiv
    (quotientKerAlgEquivOfSurjective f hf)).2
  exact ⟨{
    Vertex := Q
    vertexFintype := inferInstance
    quiver := inferInstance
    arrowFintype := fun _ _ ↦ inferInstance
    presentation := P.pathSupportHullStringPresentation }⟩

theorem relativeHullKernelRow_ne_bot_of_vertexProjectiveLabel_mem
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (z : Q)
    (hz : P.quotientVertexProjectiveLabel S z ∈
      S.nonuniserialProjectiveInjectiveLabels) :
    P.relativeHullKernelRow z ≠ ⊥ := by
  classical
  intro hrow
  let hP := P.quotientCategoryRepresentables
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let C := Category.{u, u, u} P.relations
  let iz := Fintype.equivFin C (obj P.relations z)
  let projector :=
    CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
      hP iz
  let M : RightModule.FinitelyGeneratedCategory P.quotientCategoryAlgebra :=
    RightModule.rightIdealFGObj projector
  let PP := P.quotientCategoryPrimitiveProjectivePresentation S
  let pz := P.quotientVertexProjectiveLabel S z
  have hidempotent : PP.idempotent pz = projector :=
    P.quotientCategoryPrimitiveProjectivePresentation_idempotent_vertex S z
  let eIdempotent : M ≅ RightModule.rightIdealFGObj (PP.idempotent pz) :=
    eqToIso (by rw [hidempotent])
  let eM : M ≅ S.fgObj pz.label :=
    eIdempotent.trans (PP.primitiveProjectiveIso pz)
  have hzProperties :=
    (S.mem_nonuniserialProjectiveInjectiveLabels_iff pz).1 hz
  have hMInjective : Injective M :=
    Injective.of_iso eM.symm hzProperties.1
  have hMNotUniserial :
      ¬ IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ M := by
    intro hM
    exact hzProperties.2
      (IsUniserialModule.congr (FGModuleCat.isoToLinearEquiv eM) hM)
  let I := TwoSidedIdeal.ker P.relativeHullAlgebraHom
  have hAnn : RightModule.IsAnnihilatedBy I M := by
    dsimp only [M]
    intro m a ha
    apply Subtype.ext
    change m.1 * a = 0
    have hRight : m.1 * a ∈ RightModule.rightIdeal projector := by
      simpa using (RightModule.rightIdeal projector).smul_mem
        (MulOpposite.op a) m.property
    let qma : P.relativeHullKernelRow z :=
      ⟨⟨m.1 * a, by
          simpa [projector, iz, C] using hRight⟩,
        I.mul_mem_left m.1 a ha⟩
    have hqmaBot : qma.1 ∈
        (⊥ : Submodule P.quotientCategoryAlgebraᵐᵒᵖ
          (RightModule.rightIdeal
            (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
              hP (Fintype.equivFin C (obj P.relations z))))) := by
      rw [← hrow]
      exact qma.property
    have hqma : qma.1 = 0 := by simpa using hqmaBot
    exact congrArg Subtype.val hqma
  letI : IsNoetherianRing (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Eq := RightModule.idealQuotientEquivalence (k := k) I
  let CQuot := RightModule.IdealQuotientSubcategory I
  letI : HasFiniteProducts CQuot :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      Eq.functor⟩
  letI : Abelian CQuot := CategoryTheory.abelianOfEquivalence Eq.functor
  let subM : CQuot := ⟨M, hAnn⟩
  let MQ := Eq.functor.obj subM
  letI : Projective M :=
    RightModule.rightIdealFGObj_projective
      ((CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector_complete
        hP).idem iz)
  letI : Injective M := hMInjective
  letI : Projective MQ :=
    RightModule.idealQuotientFGObj_projective_of_ambient I M hAnn inferInstance
  letI : Injective MQ :=
    RightModule.idealQuotientFGObj_injective_of_ambient I M hAnn inferInstance
  have hMIndecomposable : Indecomposable M :=
    RightModule.rightIdealFGObj_indecomposable
      (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector_primitive
        hP (fun X ↦ P.toPresentation.admissible.quotientEnd_isLocalRing X) iz)
  have hSubMIndecomposable : Indecomposable subM :=
    (RightModule.FiniteIndecomposableSkeleton.idealQuotientSubcategory_indecomposable_iff_ambient
      I subM).2 hMIndecomposable
  have hMQIndecomposable : Indecomposable MQ :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      Eq.functor subM).2
        hSubMIndecomposable
  have hMQModuleIndecomposable :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ MQ :=
    (RightModule.FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := RightModule.idealQuotientAlgebra I) MQ).2
        hMQIndecomposable
  have hMQUniserial :
      IsUniserialModule (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ MQ :=
    projectiveInjectiveIndecomposable_isUniserial_of_admitsStringPresentation
      (P.relativeHullQuotient_admitsStringPresentation) MQ
        hMQModuleIndecomposable
  apply hMNotUniserial
  exact (RightModule.idealQuotientFGObj_isUniserial_iff_ambient
    I subM).1 hMQUniserial

theorem vertexSocleIdeal_le_relativeHullKernel
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (z : Q)
    (hz : P.quotientVertexProjectiveLabel S z ∈
      S.nonuniserialProjectiveInjectiveLabels) :
    (P.quotientCategoryPrimitiveProjectivePresentation S
      ).primitiveProjectiveSocleIdeal
        (P.quotientVertexProjectiveLabel S z)
        (S.nonuniserialProjectiveInjectiveLabels_injective
          (P.quotientVertexProjectiveLabel S z) hz) ≤
      TwoSidedIdeal.ker P.relativeHullAlgebraHom := by
  classical
  let hP := P.quotientCategoryRepresentables
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let C := Category.{u, u, u} P.relations
  let iz := Fintype.equivFin C (obj P.relations z)
  let projector :=
    CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector
      hP iz
  let M : RightModule.FinitelyGeneratedCategory P.quotientCategoryAlgebra :=
    RightModule.rightIdealFGObj projector
  let PP := P.quotientCategoryPrimitiveProjectivePresentation S
  let pz := P.quotientVertexProjectiveLabel S z
  have hidempotent : PP.idempotent pz = projector :=
    P.quotientCategoryPrimitiveProjectivePresentation_idempotent_vertex S z
  let eIdempotent : M ≅ RightModule.rightIdealFGObj (PP.idempotent pz) :=
    eqToIso (by rw [hidempotent])
  let eM : M ≅ S.fgObj pz.label :=
    eIdempotent.trans (PP.primitiveProjectiveIso pz)
  have hTargetInjective : Injective (S.fgObj pz.label) :=
    S.nonuniserialProjectiveInjectiveLabels_injective pz hz
  letI : Injective M := Injective.of_iso eM.symm hTargetInjective
  have hMIndecomposable : Indecomposable M :=
    RightModule.rightIdealFGObj_indecomposable
      (CoveringHom.finiteCategoryProjectiveGenerator.smallCanonicalProjector_primitive
        hP (fun X ↦ P.toPresentation.admissible.quotientEnd_isLocalRing X) iz)
  have hsocleSimple : IsSimpleModule P.quotientCategoryAlgebraᵐᵒᵖ
      (moduleSocle P.quotientCategoryAlgebraᵐᵒᵖ M) :=
    moduleSocle_isSimple_of_injective_indecomposable
      (k := k) M hMIndecomposable
  have hrowNe : P.relativeHullKernelRow z ≠ ⊥ :=
    P.relativeHullKernelRow_ne_bot_of_vertexProjectiveLabel_mem S z hz
  have hrowLe : P.relativeHullKernelRow z ≤
      moduleSocle P.quotientCategoryAlgebraᵐᵒᵖ M :=
    P.relativeHullKernelRow_le_moduleSocle_of_ne_bot z hrowNe
  have hrowEq : P.relativeHullKernelRow z =
      moduleSocle P.quotientCategoryAlgebraᵐᵒᵖ M :=
    (isSimpleModule_iff_isAtom.mp hsocleSimple).le_iff_eq hrowNe |>.mp hrowLe
  intro a ha
  rw [PP.mem_primitiveProjectiveSocleIdeal] at ha
  change a ∈
    (moduleSocle P.quotientCategoryAlgebraᵐᵒᵖ
      (RightModule.rightIdealFGObj (PP.idempotent pz))).map
        (RightModule.rightIdeal (PP.idempotent pz)).subtype at ha
  rw [hidempotent] at ha
  obtain ⟨y, hySocle, hya⟩ := (Submodule.mem_map).1 ha
  have hyRow : y ∈ P.relativeHullKernelRow z := by
    rw [hrowEq]
    exact hySocle
  rw [← hya]
  exact hyRow

theorem socleFamily_le_relativeHullKernel
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    (P.quotientCategoryPrimitiveProjectivePresentation S
      ).primitiveProjectiveSocleFamilyIdeal
        S.nonuniserialProjectiveInjectiveLabels
        S.nonuniserialProjectiveInjectiveLabels_injective ≤
      TwoSidedIdeal.ker P.relativeHullAlgebraHom := by
  rw [RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation.primitiveProjectiveSocleFamilyIdeal]
  apply iSup_le
  intro p
  obtain ⟨z, hz⟩ := P.quotientVertexProjectiveLabel_surjective S p.1
  simpa [hz] using
    P.vertexSocleIdeal_le_relativeHullKernel S z (by simpa [hz] using p.2)

theorem relativeHullKernel_eq_socleFamily
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    TwoSidedIdeal.ker P.relativeHullAlgebraHom =
      (P.quotientCategoryPrimitiveProjectivePresentation S
        ).primitiveProjectiveSocleFamilyIdeal
          S.nonuniserialProjectiveInjectiveLabels
          S.nonuniserialProjectiveInjectiveLabels_injective := by
  apply le_antisymm
  · exact P.relativeHullKernel_le_socleFamily S
  · exact P.socleFamily_le_relativeHullKernel S

theorem quotientCategorySocleFamily_admitsStringPresentation
    [IsAlgClosed k]
    (P : SpecialBiserialPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    AdmitsStringPresentation k
      (RightModule.idealQuotientAlgebra
        ((P.quotientCategoryPrimitiveProjectivePresentation S
          ).primitiveProjectiveSocleFamilyIdeal
            S.nonuniserialProjectiveInjectiveLabels
            S.nonuniserialProjectiveInjectiveLabels_injective)) := by
  rw [← P.relativeHullKernel_eq_socleFamily S]
  exact P.relativeHullQuotient_admitsStringPresentation

end MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

namespace MagnitudeConjecture

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

theorem specialBiserial_socleFamilyQuotient_admitsStringPresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (P : S.PrimitiveProjectivePresentation)
    (hSpecial : BoundQuiver.IsSpecialBiserial k A) :
    BoundQuiver.AdmitsStringPresentation k
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonuniserialProjectiveInjectiveLabels
          S.nonuniserialProjectiveInjectiveLabels_injective)) := by
  obtain ⟨N⟩ := P.ambient_admitsSpecialBiserialPresentation_of_isSpecialBiserial
    hSpecial
  letI : Fintype N.Vertex := N.vertexFintype
  letI : Quiver.{u} N.Vertex := N.quiver
  letI (x y : N.Vertex) : Fintype (x ⟶ y) := N.arrowFintype x y
  let R := N.presentation
  let hR := R.quotientCategoryRepresentables
  letI : FiniteDimensional k R.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hR
  letI : IsNoetherianRing R.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let f : A ≃ₐ[k] R.quotientCategoryAlgebra :=
    R.toPresentation.algebraEquiv
  let T := S.mapAlgEquiv f
  let PT : T.PrimitiveProjectivePresentation := P.mapAlgEquiv f
  let PR : T.PrimitiveProjectivePresentation :=
    R.quotientCategoryPrimitiveProjectivePresentation T
  have hStringR : BoundQuiver.AdmitsStringPresentation k
      (RightModule.idealQuotientAlgebra
        (PR.primitiveProjectiveSocleFamilyIdeal
          T.nonuniserialProjectiveInjectiveLabels
          T.nonuniserialProjectiveInjectiveLabels_injective)) :=
    R.quotientCategorySocleFamily_admitsStringPresentation T
  have hIdeals :
      PR.primitiveProjectiveSocleFamilyIdeal
          T.nonuniserialProjectiveInjectiveLabels
          T.nonuniserialProjectiveInjectiveLabels_injective =
        PT.primitiveProjectiveSocleFamilyIdeal
          T.nonuniserialProjectiveInjectiveLabels
          T.nonuniserialProjectiveInjectiveLabels_injective :=
    PR.primitiveProjectiveSocleFamilyIdeal_eq_of_presentations PT
      T.nonuniserialProjectiveInjectiveLabels
      T.nonuniserialProjectiveInjectiveLabels_injective
  have hStringT : BoundQuiver.AdmitsStringPresentation k
      (RightModule.idealQuotientAlgebra
        (PT.primitiveProjectiveSocleFamilyIdeal
          T.nonuniserialProjectiveInjectiveLabels
          T.nonuniserialProjectiveInjectiveLabels_injective)) := by
    rw [← hIdeals]
    exact hStringR
  exact (BoundQuiver.admitsStringPresentation_iff_of_algEquiv
    (P.canonicalSocleFamilyQuotientAlgEquiv f)).2 hStringT

end MagnitudeConjecture
