import MagnitudeConjecture.Algebra.RightModuleSupportQuotient
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraBridge
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates

/-!
# Canonical primitive projectors of a finite linear category

The endomorphism algebra of the biproduct of all covariant representables has
the evident complete orthogonal idempotents given by its summand projectors.
This file matches those projectors with the indecomposable projective labels
of an arbitrary finite algebra-module skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.CoveringHom

universe u w z

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]

theorem biproductProjector_primitive
    {ι : Type z} [Fintype ι]
    {D : Type w} [Category.{u} D] [Preadditive D]
    (F : ι → D) [HasBiproduct F] (x : ι)
    [IsLocalRing (End (F x))] (hF : ¬ IsZero (F x)) :
    @RightModule.PrimitiveIdempotentData (End (⨁ F))
      Preadditive.instRingEnd
      (biproduct.π F x ≫ biproduct.ι F x) := by
  let e : End (⨁ F) := biproduct.π F x ≫ biproduct.ι F x
  refine
    { idempotent := by
        rw [IsIdempotentElem, End.mul_def]
        simp [Category.assoc]
      nonzero := ?_
      corner_idempotent := ?_ }
  · intro he
    apply hF
    apply (IsZero.iff_id_eq_zero (F x)).2
    have he' :
        (e : (⨁ F) ⟶ (⨁ F)) =
          (0 : (⨁ F) ⟶ (⨁ F)) := he
    have h := congrArg
      (fun q : (⨁ F) ⟶ (⨁ F) ↦
        biproduct.ι F x ≫ q ≫ biproduct.π F x) he'
    simpa [e, Category.assoc] using h
  · intro b hb heb hbe
    let c : End (F x) :=
      biproduct.ι F x ≫ b ≫ biproduct.π F x
    have hbcomp : b ≫ b = b := by
      change b ≫ b = b at hb
      exact hb
    have hbecomp : e ≫ b = b := by
      change e ≫ b = b at hbe
      exact hbe
    have hebcomp : b ≫ e = b := by
      change b ≫ e = b at heb
      exact heb
    have hsandwich : b = e ≫ b ≫ e := by
      calc
        b = e ≫ b := hbecomp.symm
        _ = e ≫ b ≫ e := by rw [hebcomp]
    have hc : IsIdempotentElem c := by
      change c * c = c
      rw [End.mul_def]
      apply End.ext
      have hmiddle := congrArg
        (fun q : End (⨁ F) ↦
          biproduct.ι F x ≫ b ≫ q ≫ biproduct.π F x)
        hbecomp
      have hsquare :
          c ≫ c =
            biproduct.ι F x ≫ b ≫ b ≫ biproduct.π F x := by
        simpa [c, e, Category.assoc] using hmiddle
      rw [hsquare]
      have hcontract := congrArg
        (fun q : End (⨁ F) ↦
          biproduct.ι F x ≫ q ≫ biproduct.π F x)
        hbcomp
      simpa [c, Category.assoc] using hcontract
    rcases
        QuotientSubmoduleEquidistribution.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
          hc with hc0 | hc1
    · left
      have hc0' :
          (c : F x ⟶ F x) = (0 : F x ⟶ F x) := hc0
      calc
        b = e ≫ b ≫ e := hsandwich
        _ = biproduct.π F x ≫ c ≫ biproduct.ι F x := by
          simp only [e, c, Category.assoc]
        _ = 0 := by rw [hc0']; simp
    · right
      have hc1' :
          (c : F x ⟶ F x) = (𝟙 (F x) : F x ⟶ F x) := hc1
      have hcOne :
          biproduct.π F x ≫ (c : F x ⟶ F x) ≫ biproduct.ι F x =
            (e : (⨁ F) ⟶ (⨁ F)) := by
        rw [hc1']
        simp [e]
      have hsandwich' :
          (b : (⨁ F) ⟶ (⨁ F)) = e ≫ b ≫ e := hsandwich
      have hmiddle :
          (e ≫ b ≫ e : (⨁ F) ⟶ (⨁ F)) =
            biproduct.π F x ≫ (c : F x ⟶ F x) ≫ biproduct.ι F x := by
        simp only [e, c, Category.assoc]
      apply End.ext
      exact hsandwich'.trans (hmiddle.trans hcOne)

namespace finiteCategoryProjectiveGenerator

variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

private abbrev representable (X : C) :
    FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k :=
  (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X)

local instance algebraFiniteDimensional :
    FiniteDimensional k (algebra hP) :=
  algebra_finiteDimensional hP

local instance algebraOppositeIsNoetherian :
    IsNoetherianRing (algebra hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k (algebra hP)ᵐᵒᵖ

/-- The projector onto one representable summand of the finite projective
generator. -/
def canonicalProjector (X : C) : algebra hP :=
  biproduct.π (representable hP) X ≫
    biproduct.ι (representable hP) X

/-- The representable summand projectors are a complete orthogonal family. -/
theorem canonicalProjector_complete :
    CompleteOrthogonalIdempotents (canonicalProjector hP) where
  idem X := by
    rw [IsIdempotentElem, End.mul_def]
    simp [canonicalProjector, Category.assoc]
  ortho X Y hXY := by
    change canonicalProjector hP X * canonicalProjector hP Y = 0
    rw [End.mul_def]
    simp only [canonicalProjector, Category.assoc]
    rw [← Category.assoc
      (biproduct.ι (representable hP) Y)
      (biproduct.π (representable hP) X),
      biproduct.ι_π_ne _ (Ne.symm hXY), zero_comp, comp_zero]
  complete := by
    change
      (∑ X : C,
        biproduct.π (representable hP) X ≫
          biproduct.ι (representable hP) X) = 𝟙 _
    exact biproduct.total

/-- A summand projector is primitive when the corresponding representable has
local endomorphism ring. -/
theorem canonicalProjector_primitive
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    RightModule.PrimitiveIdempotentData (canonicalProjector hP X) := by
  letI : IsLocalRing (End (representable hP X)) :=
    finiteDimensionalLinearCoyoneda_end_isLocalRing hP hlocal X
  exact biproductProjector_primitive (representable hP) X
    (finiteDimensionalLinearCoyoneda_indecomposable hP hlocal X).1

/-- The principal right ideal of a summand projector is the module represented
by that summand. -/
def canonicalRightIdealLinearEquiv (X : C) :
    RightModule.rightIdealFGObj (canonicalProjector hP X) ≃ₗ[
      (algebra hP)ᵐᵒᵖ]
      (representedFGFunctor hP).obj (representable hP X) where
  toFun q := q.1 ≫ biproduct.π (representable hP) X
  invFun f := ⟨f ≫ biproduct.ι (representable hP) X, ⟨
    f ≫ biproduct.ι (representable hP) X, by
      change
        (f ≫ biproduct.ι (representable hP) X) ≫
            canonicalProjector hP X =
          f ≫ biproduct.ι (representable hP) X
      simp [canonicalProjector, Category.assoc]⟩⟩
  map_add' q r := by
    change
      (q.1 + r.1) ≫ biproduct.π (representable hP) X =
        q.1 ≫ biproduct.π (representable hP) X +
          r.1 ≫ biproduct.π (representable hP) X
    exact Preadditive.add_comp
      (finiteCategoryProjectiveGenerator hP)
      (finiteCategoryProjectiveGenerator hP) (representable hP X)
      q.1 r.1 (biproduct.π (representable hP) X)
  map_smul' a q := by
    change
      a.unop ≫ q.1 ≫ biproduct.π (representable hP) X =
        a.unop ≫ (q.1 ≫ biproduct.π (representable hP) X)
    rfl
  left_inv q := by
    apply Subtype.ext
    change
      (q.1 : algebra hP) ≫ canonicalProjector hP X = q.1
    have hfixed := RightModule.rightIdeal_fixed
      ((canonicalProjector_complete hP).idem X) q
    change (q.1 : algebra hP) ≫ canonicalProjector hP X = q.1 at hfixed
    exact hfixed
  right_inv f := by
    change
      f ≫ biproduct.ι (representable hP) X ≫
          biproduct.π (representable hP) X = f
    simp

/-- Categorical form of the identification between a canonical principal
right ideal and its represented covariant representable. -/
def canonicalRightIdealIso (X : C) :
    RightModule.rightIdealFGObj (canonicalProjector hP X) ≅
      (representedFGFunctor hP).obj (representable hP X) :=
  QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
    (algebra hP)ᵐᵒᵖ (canonicalRightIdealLinearEquiv (k := k) hP X)

/-- The canonical projector coordinate of a represented category module is
its value at the matching category object. -/
def canonicalProjectorCoordinateLinearEquiv
    (X : C)
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k) :
    RightModule.idempotentCoordinate (k := k) (canonicalProjector hP X)
        ((representedFGFunctor hP).obj M) ≃ₗ[k]
      M.obj.obj.obj X := by
  let F := representedFGFunctor hP
  letI : F.Linear k := representedFGFunctor_linear hP
  let hmap :
      (representable hP X ⟶ M) ≃ₗ[k]
        (F.obj (representable hP X) ⟶ F.obj M) :=
    LinearEquiv.ofBijective (F.mapLinearMap k)
      ⟨F.map_injective, F.map_surjective⟩
  exact
    ((RightModule.rightIdealHomCoordinateEquiv
      ((canonicalProjector_complete hP).idem X) (F.obj M)).symm.trans
      (CategoryTheory.Linear.homCongr k
        (canonicalRightIdealIso (k := k) hP X) (Iso.refl (F.obj M)))).trans
      (hmap.symm.trans
        ((InducedCategory.homLinearEquiv (R := k)).trans
          (linearCoyonedaHomEquiv M.obj X)))

variable (hlocal : ∀ X : C, IsLocalRing (End X))
variable (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP))

/-- Transporting a represented module to the chosen algebra skeleton does not
change its canonical primitive coordinate. -/
def canonicalSkeletonCoordinateLinearEquiv
    (X : C)
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)
    (i : Fin S.n)
    (eM : (representedFGFunctor hP).obj M ≅ S.fgObj i) :
    RightModule.idempotentCoordinate (k := k) (canonicalProjector hP X)
        (S.fgObj i) ≃ₗ[k]
      M.obj.obj.obj X :=
  (((RightModule.rightIdealHomCoordinateEquiv
      ((canonicalProjector_complete hP).idem X) (S.fgObj i)).symm.trans
    (CategoryTheory.Linear.homCongr k
      (Iso.refl (RightModule.rightIdealFGObj (canonicalProjector hP X)))
      eM.symm)).trans
    (RightModule.rightIdealHomCoordinateEquiv
      ((canonicalProjector_complete hP).idem X)
      ((representedFGFunctor hP).obj M))).trans
    (canonicalProjectorCoordinateLinearEquiv (k := k) hP X M)

/-- The primitive multiplicity attached to a deleted category object is the
dimension of the corresponding category-module fiber. -/
theorem primitiveMultiplicity_eq_finrank_obj
    (X : C)
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)
    (i : Fin S.n)
    (eM : (representedFGFunctor hP).obj M ≅ S.fgObj i) :
    S.primitiveMultiplicity (canonicalProjector_primitive hP hlocal X) i =
      Module.finrank k (M.obj.obj.obj X) :=
  (canonicalSkeletonCoordinateLinearEquiv (k := k) hP S X M i eM).finrank_eq

/-- The projective-skeleton label represented by one canonical summand
projector. -/
def canonicalSourceLabel (X : C) : S.ProjectiveLabel :=
  S.primitiveSourceProjectiveLabel
    (canonicalProjector_primitive hP hlocal X)

/-- The represented covariant representable is the chosen skeleton object at
the source label of its canonical projector. -/
def canonicalRepresentableSourceIso (X : C) :
    (representedFGFunctor hP).obj (representable hP X) ≅
      S.fgObj (canonicalSourceLabel hP hlocal S X).label :=
  (canonicalRightIdealIso (k := k) hP X).symm ≪≫
    S.primitiveSourceIso (canonicalProjector_primitive hP hlocal X)

/-- Distinct objects have distinct canonical projective-source labels in a
skeletal finite category. -/
theorem canonicalSourceLabel_injective (hskel : Skeletal C) :
    Function.Injective (canonicalSourceLabel hP hlocal S) := by
  intro X Y hXY
  apply hskel
  apply Nonempty.intro
  let eTarget :
      (representedFGFunctor hP).obj (representable hP X) ≅
        (representedFGFunctor hP).obj (representable hP Y) :=
    (canonicalRepresentableSourceIso hP hlocal S X).trans
      ((eqToIso (congrArg (fun p : S.ProjectiveLabel ↦
        S.fgObj p.label) hXY)).trans
        (canonicalRepresentableSourceIso hP hlocal S Y).symm)
  let eRepresentable : representable hP X ≅ representable hP Y :=
    (representedFGFunctor hP).preimageIso eTarget
  let J := finiteDimensionalLinearCoyonedaFunctor (k := k) hP
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

/-- Every indecomposable projective in the algebra-module skeleton is the
source of one canonical summand projector. -/
theorem canonicalSourceLabel_surjective :
    Function.Surjective (canonicalSourceLabel hP hlocal S) := by
  intro p
  let E := moduleEquivalence hP
  letI : E.functor.Additive :=
    { map_add := by
        intro X Y f g
        change (representedFGFunctor hP).map (f + g) =
          (representedFGFunctor hP).map f +
            (representedFGFunctor hP).map g
        exact (representedFGFunctor hP).map_add }
  letI : E.inverse.Additive := inferInstance
  let P := E.inverse.obj (S.fgObj p.label)
  have hPind : Indecomposable P :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse (S.fgObj p.label)).2 (S.fgObj_indecomposable p.label)
  letI : Projective P :=
    (E.symm.map_projective_iff (S.fgObj p.label)).2 p.projective
  obtain ⟨X, ⟨eX⟩⟩ :=
    indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      hP hlocal P hPind
  let eTarget :
      (representedFGFunctor hP).obj (representable hP X) ≅
        S.fgObj p.label :=
    (E.functor.mapIso eX).trans (E.counitIso.app (S.fgObj p.label))
  have hlabel : (canonicalSourceLabel hP hlocal S X).label = p.label :=
    S.fgObj_skeletal ⟨
      (canonicalRepresentableSourceIso hP hlocal S X).symm.trans eTarget⟩
  refine ⟨X, ?_⟩
  let q := canonicalSourceLabel hP hlocal S X
  have hlabel' : q.label = p.label := hlabel
  change q = p
  rcases hq : q with ⟨j, hj⟩
  rcases hp : p with ⟨i, hi⟩
  rw [hq, hp] at hlabel'
  change j = i at hlabel'
  subst i
  rfl

/-- The canonical summands and the projective labels of any duplicate-free
algebra-module skeleton have the same indexing set. -/
def canonicalSourceEquiv (hskel : Skeletal C) :
    C ≃ S.ProjectiveLabel :=
  Equiv.ofBijective (canonicalSourceLabel hP hlocal S)
    ⟨canonicalSourceLabel_injective hP hlocal S hskel,
      canonicalSourceLabel_surjective hP hlocal S⟩

/-- The canonical primitive projectors, reindexed by the chosen projective
skeleton, form the primitive-projective presentation required by the
algebraic deletion theorem. -/
def primitiveProjectivePresentation (hskel : Skeletal C) :
    S.PrimitiveProjectivePresentation where
  idempotent p :=
    canonicalProjector hP ((canonicalSourceEquiv hP hlocal S hskel).symm p)
  complete :=
    (CompleteOrthogonalIdempotents.equiv
      (e := canonicalProjector hP)
      (canonicalSourceEquiv hP hlocal S hskel).symm).2
        (canonicalProjector_complete hP)
  primitive p :=
    canonicalProjector_primitive hP hlocal
      ((canonicalSourceEquiv hP hlocal S hskel).symm p)
  sourceLabel p := by
    change canonicalSourceLabel hP hlocal S
      ((canonicalSourceEquiv hP hlocal S hskel).symm p) = p
    exact (canonicalSourceEquiv hP hlocal S hskel).apply_symm_apply p

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
