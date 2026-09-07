import MagnitudeConjecture.Algebra.RightModulePrimitiveArrowGain

/-!
# Irreducible-arrow descent under primitive deletion

Inflation identifies the Hom and radical spaces between two modules over
`A / AeA` with their ambient counterparts.  A quotient radical-square
factorization is still a radical-square factorization after inflation, while
the ambient category may have additional intermediate modules.  Consequently
there is a canonical surjection `Irr_(A/AeA)(X,Y) ⟶ Irr_A(X,Y)`, giving the
arrow-multiplicity inequality used in the live manuscript.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : RightModule.PrimitiveIdempotentData e)
variable [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]

noncomputable local instance primitiveArrowDescentQuotientFintype :
    Fintype (S.PrimitiveQuotientLabel D) :=
  Fintype.ofFinite _

/-- Inflation from the primitive quotient to ambient finitely generated right
modules. -/
def primitiveQuotientInflationFunctor :
    RightModule.FinitelyGeneratedCategory
        (RightModule.primitiveQuotientAlgebra e) ⥤
      RightModule.FinitelyGeneratedCategory A :=
  (RightModule.primitiveQuotientEquivalence (k := k) e).inverse ⋙
    (RightModule.PrimitiveQuotientProperty e).ι

noncomputable local instance primitiveQuotientInflationFunctorAdditive :
    (primitiveQuotientInflationFunctor
      (k := k) (A := A) (e := e)).Additive := by
  dsimp [primitiveQuotientInflationFunctor]
  infer_instance

noncomputable local instance primitiveQuotientInflationFunctorLinear :
    (primitiveQuotientInflationFunctor
      (k := k) (A := A) (e := e)).Linear k := by
  dsimp [primitiveQuotientInflationFunctor]
  infer_instance

local instance primitiveQuotientInflationFunctorFull :
    (primitiveQuotientInflationFunctor
      (k := k) (A := A) (e := e)).Full := by
  dsimp [primitiveQuotientInflationFunctor]
  infer_instance

local instance primitiveQuotientInflationFunctorFaithful :
    (primitiveQuotientInflationFunctor
      (k := k) (A := A) (e := e)).Faithful := by
  dsimp [primitiveQuotientInflationFunctor]
  infer_instance

/-- Inflation of a literal quotient representative recovers its ambient
representative. -/
def primitiveQuotientInflationObjIso
    (x : S.PrimitiveQuotientLabel D) :
    (primitiveQuotientInflationFunctor (k := k) (A := A) (e := e)).obj
        (S.primitiveQuotientFGObj D x) ≅
      S.fgObj x.1 := by
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  exact U.mapIso
    (E.unitIso.app (S.primitiveQuotientLabelObj D x)).symm

/-- Inflation and the endpoint identifications give the common Hom space
between two surviving indecomposables. -/
def primitiveQuotientHomAmbientLinearEquiv
    (x y : S.PrimitiveQuotientLabel D) :
    (S.primitiveQuotientFGObj D x ⟶
        S.primitiveQuotientFGObj D y) ≃ₗ[k]
      (S.fgObj x.1 ⟶ S.fgObj y.1) :=
  (LinearEquiv.ofBijective
      ((primitiveQuotientInflationFunctor
        (k := k) (A := A) (e := e)).mapLinearMap k)
      ⟨(primitiveQuotientInflationFunctor
          (k := k) (A := A) (e := e)).map_injective,
        (primitiveQuotientInflationFunctor
          (k := k) (A := A) (e := e)).map_surjective⟩).trans
    (CategoryTheory.Linear.homCongr k
      (S.primitiveQuotientInflationObjIso D x)
      (S.primitiveQuotientInflationObjIso D y))

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
@[simp]
theorem primitiveQuotientHomAmbientLinearEquiv_apply
    (x y : S.PrimitiveQuotientLabel D)
    (f : S.primitiveQuotientFGObj D x ⟶
      S.primitiveQuotientFGObj D y) :
    S.primitiveQuotientHomAmbientLinearEquiv D x y f =
      (S.primitiveQuotientInflationObjIso D x).inv ≫
        (primitiveQuotientInflationFunctor
          (k := k) (A := A) (e := e)).map f ≫
          (S.primitiveQuotientInflationObjIso D y).hom := by
  simp only [primitiveQuotientHomAmbientLinearEquiv,
    LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    CategoryTheory.Linear.homCongr_apply, Category.assoc]
  rw [show ((primitiveQuotientInflationFunctor
    (k := k) (A := A) (e := e)).mapLinearMap k) f =
      (primitiveQuotientInflationFunctor
        (k := k) (A := A) (e := e)).map f by rfl]

/-- The common Hom-space identification at the level of underlying linear
maps used by the irreducible-Hom API. -/
def primitiveQuotientLinearMapAmbientLinearEquiv
    (x y : S.PrimitiveQuotientLabel D) :
    (S.primitiveQuotientFGObj D x →ₗ[
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]
      S.primitiveQuotientFGObj D y) ≃ₗ[k]
      (S.fgObj x.1 →ₗ[Aᵐᵒᵖ] S.fgObj y.1) :=
  (((InducedCategory.homLinearEquiv (R := k)).trans
      (ModuleCat.homLinearEquiv (S := k))).symm.trans
    (S.primitiveQuotientHomAmbientLinearEquiv D x y)).trans
      ((InducedCategory.homLinearEquiv (R := k)).trans
        (ModuleCat.homLinearEquiv (S := k)))

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
@[simp]
theorem primitiveQuotientLinearMapAmbientLinearEquiv_ofHom
    (x y : S.PrimitiveQuotientLabel D)
    (f : S.primitiveQuotientFGObj D x →ₗ[
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]
      S.primitiveQuotientFGObj D y) :
    (ConcreteCategory.ofHom
        (S.primitiveQuotientLinearMapAmbientLinearEquiv D x y f) :
      S.fgObj x.1 ⟶ S.fgObj y.1) =
      S.primitiveQuotientHomAmbientLinearEquiv D x y
        (ConcreteCategory.ofHom f) :=
  rfl

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- Inflation preserves and reflects split epimorphisms between the fixed
surviving representatives. -/
theorem primitiveQuotientHomAmbientLinearEquiv_isSplitEpi_iff
    (x y : S.PrimitiveQuotientLabel D)
    (f : S.primitiveQuotientFGObj D x ⟶
      S.primitiveQuotientFGObj D y) :
    IsSplitEpi (S.primitiveQuotientHomAmbientLinearEquiv D x y f) ↔
      IsSplitEpi f := by
  let F := primitiveQuotientInflationFunctor
    (k := k) (A := A) (e := e)
  let ex := S.primitiveQuotientInflationObjIso D x
  let ey := S.primitiveQuotientInflationObjIso D y
  rw [S.primitiveQuotientHomAmbientLinearEquiv_apply D x y f]
  constructor
  · intro hsplit
    letI : IsSplitEpi (ex.inv ≫ F.map f ≫ ey.hom) := hsplit
    have hmap : IsSplitEpi (F.map f) := by
      rw [show F.map f = ex.hom ≫
          (ex.inv ≫ F.map f ≫ ey.hom) ≫ ey.inv by simp]
      infer_instance
    exact (F.isSplitEpi_iff f).1 hmap
  · intro hsplit
    have hmap : IsSplitEpi (F.map f) :=
      (F.isSplitEpi_iff f).2 hsplit
    letI : IsSplitEpi (F.map f) := hmap
    infer_instance

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- The underlying common-Hom equivalence preserves and reflects split
epimorphisms. -/
theorem primitiveQuotientLinearMapAmbientLinearEquiv_isSplitEpi_iff
    (x y : S.PrimitiveQuotientLabel D)
    (f : S.primitiveQuotientFGObj D x →ₗ[
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]
      S.primitiveQuotientFGObj D y) :
    IsSplitEpi (ConcreteCategory.ofHom
      (S.primitiveQuotientLinearMapAmbientLinearEquiv D x y f) :
        S.fgObj x.1 ⟶ S.fgObj y.1) ↔
      IsSplitEpi (ConcreteCategory.ofHom f :
        S.primitiveQuotientFGObj D x ⟶
          S.primitiveQuotientFGObj D y) := by
  simpa only [S.primitiveQuotientLinearMapAmbientLinearEquiv_ofHom D x y f]
    using S.primitiveQuotientHomAmbientLinearEquiv_isSplitEpi_iff D x y
      (ConcreteCategory.ofHom f)

noncomputable local instance primitiveArrowDescentAmbientModule
    (i : Fin S.n) : Module k (S.almostSplitSkeleton.obj i) :=
  Module.restrictScalars k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i)

noncomputable local instance primitiveArrowDescentAmbientTower
    (i : Fin S.n) :
    IsScalarTower k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i) :=
  IsScalarTower.restrictScalars k Aᵐᵒᵖ
    (S.almostSplitSkeleton.obj i)

noncomputable local instance primitiveArrowDescentQuotientModule
    (i : S.PrimitiveQuotientLabel D) :
    Module k ((S.primitiveQuotientAlmostSplitSkeleton D).obj i) :=
  Module.restrictScalars k
    (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ
    ((S.primitiveQuotientAlmostSplitSkeleton D).obj i)

noncomputable local instance primitiveArrowDescentQuotientTower
    (i : S.PrimitiveQuotientLabel D) :
    IsScalarTower k (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ
      ((S.primitiveQuotientAlmostSplitSkeleton D).obj i) :=
  IsScalarTower.restrictScalars k
    (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ
    ((S.primitiveQuotientAlmostSplitSkeleton D).obj i)

/-- Inflation identifies the quotient and ambient radical spaces between
surviving indecomposables. -/
def primitiveQuotientRadicalAmbientLinearEquiv
    (x y : S.PrimitiveQuotientLabel D) :
    (S.primitiveQuotientAlmostSplitSkeleton D).radicalHom
        (K := k) x y ≃ₗ[k]
      S.almostSplitSkeleton.radicalHom (K := k) x.1 y.1 where
  toFun f := ⟨S.primitiveQuotientLinearMapAmbientLinearEquiv D x y f.1, by
    rw [S.almostSplitSkeleton.mem_radicalHom_iff_not_isSplitEpi]
    intro hsplit
    have hqsplit :=
      (S.primitiveQuotientLinearMapAmbientLinearEquiv_isSplitEpi_iff
        D x y f.1).1 hsplit
    exact ((S.primitiveQuotientAlmostSplitSkeleton D)
      |>.mem_radicalHom_iff_not_isSplitEpi f.1).1 f.2 hqsplit⟩
  invFun f := ⟨(S.primitiveQuotientLinearMapAmbientLinearEquiv D x y).symm f.1, by
    rw [(S.primitiveQuotientAlmostSplitSkeleton D)
      |>.mem_radicalHom_iff_not_isSplitEpi]
    intro hsplit
    have hambientSplit :=
      (S.primitiveQuotientLinearMapAmbientLinearEquiv_isSplitEpi_iff
        D x y
        ((S.primitiveQuotientLinearMapAmbientLinearEquiv D x y).symm f.1)).2
          hsplit
    have hambientNot :=
      (S.almostSplitSkeleton.mem_radicalHom_iff_not_isSplitEpi f.1).1 f.2
    change ¬ IsSplitEpi (ConcreteCategory.ofHom f.1 :
      S.fgObj x.1 ⟶ S.fgObj y.1) at hambientNot
    apply hambientNot
    simpa using hambientSplit⟩
  left_inv f := Subtype.ext <|
    (S.primitiveQuotientLinearMapAmbientLinearEquiv D x y).symm_apply_apply f.1
  right_inv f := Subtype.ext <|
    (S.primitiveQuotientLinearMapAmbientLinearEquiv D x y).apply_symm_apply f.1
  map_add' f g := Subtype.ext <|
    (S.primitiveQuotientLinearMapAmbientLinearEquiv D x y).map_add f.1 g.1
  map_smul' c f := Subtype.ext <|
    (S.primitiveQuotientLinearMapAmbientLinearEquiv D x y).map_smul c f.1

/-- Every quotient radical-square factorization remains an ambient
radical-square factorization after inflation. -/
theorem primitiveQuotientRadicalSquare_map_mem
    (x y : S.PrimitiveQuotientLabel D)
    (f : (S.primitiveQuotientAlmostSplitSkeleton D).radicalHom
      (K := k) x y)
    (hf : f ∈ ((S.primitiveQuotientAlmostSplitSkeleton D)
      |>.radicalSquareInRadicalSubmodule (K := k) x y)) :
    S.primitiveQuotientRadicalAmbientLinearEquiv D x y f ∈
      S.almostSplitSkeleton.radicalSquareInRadicalSubmodule
        (K := k) x.1 y.1 := by
  let sigmaQ := S.primitiveQuotientAlmostSplitSkeleton D
  let F := primitiveQuotientInflationFunctor
    (k := k) (A := A) (e := e)
  let ex := S.primitiveQuotientInflationObjIso D x
  let ey := S.primitiveQuotientInflationObjIso D y
  change f.1 ∈ sigmaQ.radicalSquareHomSubmodule (K := k) x y at hf
  rw [sigmaQ.mem_radicalSquareHomSubmodule_iff] at hf
  obtain ⟨M, g, h, hg, hh, hcomp⟩ := hf
  let gQ : S.primitiveQuotientFGObj D x ⟶ M := g
  let hQ : M ⟶ S.primitiveQuotientFGObj D y := h
  have hcompQ : gQ ≫ hQ = ConcreteCategory.ofHom f.1 := hcomp
  let gA : S.fgObj x.1 ⟶ F.obj M := ex.inv ≫ F.map gQ
  let hA : F.obj M ⟶ S.fgObj y.1 := F.map hQ ≫ ey.hom
  change (S.primitiveQuotientRadicalAmbientLinearEquiv D x y f).1 ∈
    S.almostSplitSkeleton.radicalSquareHomSubmodule (K := k) x.1 y.1
  rw [S.almostSplitSkeleton.mem_radicalSquareHomSubmodule_iff]
  refine ⟨F.obj M, gA, hA, ?_, ?_, ?_⟩
  · intro hsplit
    letI : IsSplitMono gA := hsplit
    have hmap : IsSplitMono (F.map g) := by
      apply IsSplitMono.mk'
      exact {
        retraction := retraction gA ≫ ex.inv
        id := by
          change F.map gQ ≫ (retraction gA ≫ ex.inv) = 𝟙 _
          rw [show F.map gQ = ex.hom ≫ gA by simp [gA]]
          simp }
    exact hg ((F.isSplitMono_iff g).1 hmap)
  · intro hsplit
    letI : IsSplitEpi hA := hsplit
    have hmap : IsSplitEpi (F.map h) := by
      apply IsSplitEpi.mk'
      exact {
        section_ := ey.hom ≫ section_ hA
        id := by
          change (ey.hom ≫ section_ hA) ≫ F.map hQ = 𝟙 _
          rw [show F.map hQ = hA ≫ ey.inv by simp [hA]]
          simp }
    exact hh ((F.isSplitEpi_iff h).1 hmap)
  · calc
      gA ≫ hA = ex.inv ≫ F.map (gQ ≫ hQ) ≫ ey.hom := by
        simp [gA, hA, Category.assoc]
      _ = ex.inv ≫
          F.map (ConcreteCategory.ofHom f.1) ≫ ey.hom := by
        rw [hcompQ]
      _ = S.primitiveQuotientHomAmbientLinearEquiv D x y
          (ConcreteCategory.ofHom f.1) := by
        rw [S.primitiveQuotientHomAmbientLinearEquiv_apply]
      _ = ConcreteCategory.ofHom
          (S.primitiveQuotientLinearMapAmbientLinearEquiv D x y f.1) := by
        rw [S.primitiveQuotientLinearMapAmbientLinearEquiv_ofHom]
      _ = ConcreteCategory.ofHom
          (S.primitiveQuotientRadicalAmbientLinearEquiv D x y f).1 := rfl

/-- The quotient-to-ambient map on irreducible morphism spaces. -/
def primitiveIrreducibleHomDescentLinearMap
    (x y : S.PrimitiveQuotientLabel D) :
    (S.primitiveQuotientAlmostSplitSkeleton D).irreducibleHomSpace
        (K := k) x y →ₗ[k]
      S.almostSplitSkeleton.irreducibleHomSpace (K := k) x.1 y.1 :=
  Submodule.mapQ
    ((S.primitiveQuotientAlmostSplitSkeleton D)
      |>.radicalSquareInRadicalSubmodule (K := k) x y)
    (S.almostSplitSkeleton.radicalSquareInRadicalSubmodule
      (K := k) x.1 y.1)
    (S.primitiveQuotientRadicalAmbientLinearEquiv D x y).toLinearMap
    (by
      intro f hf
      exact S.primitiveQuotientRadicalSquare_map_mem D x y f hf)

/-- Every ambient irreducible class between surviving modules has a quotient
irreducible-class lift. -/
theorem primitiveIrreducibleHomDescentLinearMap_surjective
    (x y : S.PrimitiveQuotientLabel D) :
    Function.Surjective
      (S.primitiveIrreducibleHomDescentLinearMap D x y) := by
  intro z
  let sigmaA := S.almostSplitSkeleton
  let sigmaQ := S.primitiveQuotientAlmostSplitSkeleton D
  obtain ⟨a, rfl⟩ :=
    (sigmaA.radicalSquareInRadicalSubmodule
      (K := k) x.1 y.1).mkQ_surjective z
  obtain ⟨q, hq⟩ :=
    (S.primitiveQuotientRadicalAmbientLinearEquiv D x y).surjective a
  refine ⟨Submodule.Quotient.mk q, ?_⟩
  change Submodule.Quotient.mk
      (S.primitiveQuotientRadicalAmbientLinearEquiv D x y q) =
    Submodule.Quotient.mk a
  rw [hq]

/-- The first assertion of the manuscript's descent lemma:
`a_(A/AeA)(X,Y) ≥ a_A(X,Y)` for surviving indecomposables. -/
theorem ambientIrreducibleArrowMultiplicity_le_primitiveQuotient
    (x y : S.PrimitiveQuotientLabel D) :
    S.ambientIrreducibleArrowMultiplicity D x y ≤
      S.primitiveQuotientIrreducibleArrowMultiplicity D x y := by
  letI : Module.Finite k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ := by
    infer_instance
  letI : Module.Finite k
      ((S.primitiveQuotientAlmostSplitSkeleton D).obj x) :=
    RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.primitiveQuotientAlgebra e)
      (S.primitiveQuotientFGObj D x)
  letI : Module.Finite k
      ((S.primitiveQuotientAlmostSplitSkeleton D).obj y) :=
    RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.primitiveQuotientAlgebra e)
      (S.primitiveQuotientFGObj D y)
  letI : Module.Finite k
      ((S.primitiveQuotientAlmostSplitSkeleton D).obj x →ₗ[
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]
        (S.primitiveQuotientAlmostSplitSkeleton D).obj y) := by
    infer_instance
  letI : Module.Finite k
      ((S.primitiveQuotientAlmostSplitSkeleton D).radicalHom
        (K := k) x y) := by
    infer_instance
  letI : Module.Finite k
      ((S.primitiveQuotientAlmostSplitSkeleton D).irreducibleHomSpace
        (K := k) x y) := by
    infer_instance
  unfold ambientIrreducibleArrowMultiplicity
    primitiveQuotientIrreducibleArrowMultiplicity
  exact LinearMap.finrank_le_finrank_of_surjective
    (S.primitiveIrreducibleHomDescentLinearMap_surjective D x y)

/-- Pointwise, quotient arrow multiplicity is ambient multiplicity plus the
defined arrow gain. -/
theorem primitiveQuotientIrreducibleArrowMultiplicity_eq_ambient_add_gain
    (x y : S.PrimitiveQuotientLabel D) :
    S.primitiveQuotientIrreducibleArrowMultiplicity D x y =
      S.ambientIrreducibleArrowMultiplicity D x y +
        S.primitiveArrowGain D x y := by
  have hle :=
    S.ambientIrreducibleArrowMultiplicity_le_primitiveQuotient D x y
  unfold primitiveArrowGain
  omega

/-- Summing the pointwise descent identity gives the manuscript's total
internal-arrow relation `a_B = a₀ + c`. -/
theorem sum_primitiveQuotientIrreducibleArrowMultiplicity_eq_ambient_add_gain :
    (∑ x : S.PrimitiveQuotientLabel D,
      ∑ y : S.PrimitiveQuotientLabel D,
        S.primitiveQuotientIrreducibleArrowMultiplicity D x y) =
      (∑ x : S.PrimitiveQuotientLabel D,
        ∑ y : S.PrimitiveQuotientLabel D,
          S.ambientIrreducibleArrowMultiplicity D x y) +
        S.primitiveTotalArrowGain D := by
  classical
  unfold primitiveTotalArrowGain
  simp_rw [S.primitiveQuotientIrreducibleArrowMultiplicity_eq_ambient_add_gain
    D, Finset.sum_add_distrib]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
