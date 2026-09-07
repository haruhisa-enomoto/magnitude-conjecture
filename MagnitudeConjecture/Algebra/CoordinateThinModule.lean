import MagnitudeConjecture.Algebra.RightModulePrimitiveIdempotent
import MagnitudeConjecture.CategoryTheory.EndomorphismDrop

/-!
# Coordinate-thin modules

For a family of idempotents in a finite-dimensional algebra, a finitely
generated right module is coordinate-thin when every space `Xe` has
coefficient-field dimension at most one.  For a basic algebra and a complete
primitive family, these dimensions are the usual simple composition-factor
multiplicities.  The definition below keeps only the coordinate statement
actually supplied by finite-category modules and used in the biseriality
argument.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} {ι : Type w} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Every chosen idempotent coordinate of a finitely generated right module
has dimension at most one. -/
def IsCoordinateThin
    (e : ι → A) (M : FinitelyGeneratedCategory A) : Prop :=
  ∀ i : ι,
    Module.finrank k (idempotentCoordinate (k := k) (e i) M) ≤ 1

/-- Every indecomposable finitely generated right module is coordinate-thin.
This is the algebraic form of the multiplicity-free premise used in the
biseriality induction. -/
def AllIndecomposablesCoordinateThin (e : ι → A) : Prop :=
  ∀ M : FinitelyGeneratedCategory A,
    Indecomposable M → IsCoordinateThin (k := k) e M

/-- A module isomorphism identifies the coordinates belonging to an
idempotent. -/
def idempotentCoordinateLinearEquivOfIso
    {e : A} (he : IsIdempotentElem e)
    {M N : FinitelyGeneratedCategory A} (f : M ≅ N) :
    idempotentCoordinate (k := k) e M ≃ₗ[k]
      idempotentCoordinate (k := k) e N :=
  ((rightIdealHomCoordinateEquiv (k := k) he M).symm.trans
    (CategoryTheory.Linear.homCongr k
      (Iso.refl (rightIdealFGObj e)) f)).trans
    (rightIdealHomCoordinateEquiv (k := k) he N)

/-- Coordinate thinness is invariant under module isomorphism. -/
theorem IsCoordinateThin.congr
    (e : ι → A) (he : ∀ i, IsIdempotentElem (e i))
    {M N : FinitelyGeneratedCategory A} (f : M ≅ N)
    (hM : IsCoordinateThin (k := k) e M) :
    IsCoordinateThin (k := k) e N := by
  intro i
  rw [← (idempotentCoordinateLinearEquivOfIso
    (k := k) (he i) f).finrank_eq]
  exact hM i

/-- A module map restricts to every idempotent coordinate. -/
def idempotentCoordinateLinearMap
    (e : A) {M N : FinitelyGeneratedCategory A}
    (f : M →ₗ[Aᵐᵒᵖ] N) :
    idempotentCoordinate (k := k) e M →ₗ[k]
      idempotentCoordinate (k := k) e N where
  toFun x := by
    refine ⟨f x.1, ?_⟩
    obtain ⟨y, hy⟩ := x.2
    refine ⟨f y, ?_⟩
    change (MulOpposite.op e) • f y = f x.1
    rw [← f.map_smul]
    exact congrArg f hy
  map_add' _ _ := by
    apply Subtype.ext
    exact f.map_add _ _
  map_smul' _ _ := by
    apply Subtype.ext
    exact f.map_smul _ _

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- An injective module map remains injective on every idempotent
coordinate. -/
theorem idempotentCoordinateLinearMap_injective
    (e : A) {M N : FinitelyGeneratedCategory A}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : Function.Injective f) :
    Function.Injective (idempotentCoordinateLinearMap (k := k) e f) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)

/-- A surjective module map remains surjective on an idempotent coordinate.
The idempotent projects any chosen preimage back into that coordinate. -/
theorem idempotentCoordinateLinearMap_surjective
    {e : A} (he : IsIdempotentElem e)
    {M N : FinitelyGeneratedCategory A}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : Function.Surjective f) :
    Function.Surjective (idempotentCoordinateLinearMap (k := k) e f) := by
  intro y
  obtain ⟨m, hm⟩ := hf y.1
  let x : idempotentCoordinate (k := k) e M :=
    ⟨(MulOpposite.op e) • m, ⟨m, rfl⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change f ((MulOpposite.op e) • m) = y.1
  rw [f.map_smul, hm]
  exact idempotentCoordinate_fixed (k := k) he N y

/-- A positive idempotent coordinate remains positive under an injective
module map. -/
theorem idempotentCoordinate_pos_of_injective
    (e : A) {M N : FinitelyGeneratedCategory A}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : Function.Injective f)
    (hM : 0 < Module.finrank k (idempotentCoordinate (k := k) e M)) :
    0 < Module.finrank k (idempotentCoordinate (k := k) e N) := by
  letI : Module.Finite k M :=
    finite_over_field_of_finitelyGenerated k A M
  letI : Module.Finite k N :=
    finite_over_field_of_finitelyGenerated k A N
  exact hM.trans_le
    (LinearMap.finrank_le_finrank_of_injective
      (idempotentCoordinateLinearMap_injective (k := k) e f hf))

/-- A positive idempotent coordinate in a quotient was already positive in
the source. -/
theorem idempotentCoordinate_pos_of_surjective
    {e : A} (he : IsIdempotentElem e)
    {M N : FinitelyGeneratedCategory A}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : Function.Surjective f)
    (hN : 0 < Module.finrank k (idempotentCoordinate (k := k) e N)) :
    0 < Module.finrank k (idempotentCoordinate (k := k) e M) := by
  letI : Module.Finite k M :=
    finite_over_field_of_finitelyGenerated k A M
  letI : Module.Finite k N :=
    finite_over_field_of_finitelyGenerated k A N
  exact hN.trans_le
    (LinearMap.finrank_le_finrank_of_surjective
      (idempotentCoordinateLinearMap_surjective (k := k) he f hf))

/-- A submodule of a finitely generated right module, retained as an object
of the finitely generated module category. -/
def submoduleFGObj
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    FinitelyGeneratedCategory A := by
  letI : Module.Finite Aᵐᵒᵖ P := inferInstance
  exact FGModuleCat.of Aᵐᵒᵖ P

/-- Inclusion of a submodule restricts to an inclusion on every idempotent
coordinate. -/
def idempotentCoordinateSubmoduleLinearMap
    (e : A) (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    idempotentCoordinate (k := k) e (submoduleFGObj M P) →ₗ[k]
      idempotentCoordinate (k := k) e M where
  toFun x := by
    refine ⟨x.1.1, ?_⟩
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y.1, congrArg Subtype.val hy⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional k A] in
/-- The coordinate inclusion belonging to a module submodule is injective.
-/
theorem idempotentCoordinateSubmoduleLinearMap_injective
    (e : A) (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    Function.Injective (idempotentCoordinateSubmoduleLinearMap
      (k := k) e M P) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : idempotentCoordinate (k := k) e M ↦ (z.1 : M)) hxy

/-- Coordinate thinness passes to finitely generated submodules. -/
theorem IsCoordinateThin.submodule
    {e : ι → A} {M : FinitelyGeneratedCategory A}
    (hM : IsCoordinateThin (k := k) e M)
    (P : Submodule Aᵐᵒᵖ M) :
    IsCoordinateThin (k := k) e (submoduleFGObj M P) := by
  intro i
  letI : Module.Finite k M :=
    finite_over_field_of_finitelyGenerated k A M
  exact (LinearMap.finrank_le_finrank_of_injective
    (idempotentCoordinateSubmoduleLinearMap_injective
      (k := k) (e i) M P)).trans (hM i)

/-- A quotient of a finitely generated right module, retained as an object
of the finitely generated module category. -/
def quotientFGObj
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    FinitelyGeneratedCategory A := by
  letI : Module.Finite Aᵐᵒᵖ (M ⧸ P) := inferInstance
  exact FGModuleCat.of Aᵐᵒᵖ (M ⧸ P)

/-- The quotient map, bundled with the finitely generated quotient wrapper as
its codomain. -/
def quotientFGMkQ
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    M →ₗ[Aᵐᵒᵖ] quotientFGObj M P where
  toFun := P.mkQ
  map_add' := P.mkQ.map_add
  map_smul' := P.mkQ.map_smul

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem quotientFGMkQ_apply
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M)
    (x : M) : quotientFGMkQ M P x = P.mkQ x := rfl

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The bundled quotient map is surjective. -/
theorem quotientFGMkQ_surjective
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    Function.Surjective (quotientFGMkQ M P) := by
  intro x
  obtain ⟨m, hm⟩ := P.mkQ_surjective x
  exact ⟨m, hm⟩

/-- A linear map killing a submodule descends to the finitely generated
quotient wrapper. -/
def quotientFGLift
    (M N : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M)
    (f : M →ₗ[Aᵐᵒᵖ] N) (hP : P ≤ f.ker) :
    quotientFGObj M P →ₗ[Aᵐᵒᵖ] N where
  toFun := P.liftQ f hP
  map_add' := (P.liftQ f hP).map_add
  map_smul' := (P.liftQ f hP).map_smul

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem quotientFGLift_apply_mkQ
    (M N : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M)
    (f : M →ₗ[Aᵐᵒᵖ] N) (hP : P ≤ f.ker) (x : M) :
    quotientFGLift M N P f hP (quotientFGMkQ M P x) = f x := by
  exact Submodule.liftQ_apply P f (h := hP) x

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- A surjective map remains surjective after it is descended across a
submodule contained in its kernel. -/
theorem quotientFGLift_surjective
    (M N : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M)
    (f : M →ₗ[Aᵐᵒᵖ] N) (hP : P ≤ f.ker)
    (hf : Function.Surjective f) :
    Function.Surjective (quotientFGLift M N P f hP) := by
  intro n
  obtain ⟨m, hm⟩ := hf n
  refine ⟨quotientFGMkQ M P m, ?_⟩
  rw [quotientFGLift_apply_mkQ, hm]

/-- The canonical map between two nested finitely generated quotients. -/
def quotientFGMapQ
    (M : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ M) (hPQ : P ≤ Q) :
    quotientFGObj M P →ₗ[Aᵐᵒᵖ] quotientFGObj M Q where
  toFun := P.mapQ Q LinearMap.id hPQ
  map_add' := (P.mapQ Q LinearMap.id hPQ).map_add
  map_smul' := (P.mapQ Q LinearMap.id hPQ).map_smul

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem quotientFGMapQ_apply_mkQ
    (M : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ M) (hPQ : P ≤ Q) (x : M) :
    quotientFGMapQ M P Q hPQ (P.mkQ x) = Q.mkQ x := by
  rfl

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Every canonical map between nested quotients is surjective. -/
theorem quotientFGMapQ_surjective
    (M : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ M) (hPQ : P ≤ Q) :
    Function.Surjective (quotientFGMapQ M P Q hPQ) := by
  intro x
  obtain ⟨m, rfl⟩ := Q.mkQ_surjective x
  exact ⟨P.mkQ m, rfl⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The kernel of the canonical map `M/P → M/Q` is the image of `Q`. -/
theorem quotientFGMapQ_ker
    (M : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ M) (hPQ : P ≤ Q) :
    (quotientFGMapQ M P Q hPQ).ker = Q.map P.mkQ := by
  change (P.mapQ Q LinearMap.id hPQ).ker = Q.map P.mkQ
  rw [Submodule.ker_mapQ]
  simp

/-- The quotient map of a module restricts to a linear map on every
idempotent coordinate. -/
def idempotentCoordinateQuotientLinearMap
    (e : A) (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    idempotentCoordinate (k := k) e M →ₗ[k]
      idempotentCoordinate (k := k) e (quotientFGObj M P) where
  toFun x := by
    refine ⟨P.mkQ x.1, ?_⟩
    obtain ⟨y, hy⟩ := x.2
    change (MulOpposite.op e) • y = x.1 at hy
    refine ⟨P.mkQ y, ?_⟩
    change (MulOpposite.op e) • P.mkQ y = P.mkQ x.1
    rw [← P.mkQ.map_smul, hy]
  map_add' _ _ := by
    apply Subtype.ext
    exact P.mkQ.map_add _ _
  map_smul' _ _ := by
    apply Subtype.ext
    exact P.mkQ.map_smul _ _

/-- For an idempotent, the coordinate map induced by a module quotient is
surjective. -/
theorem idempotentCoordinateQuotientLinearMap_surjective
    {e : A} (he : IsIdempotentElem e)
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    Function.Surjective (idempotentCoordinateQuotientLinearMap
      (k := k) e M P) := by
  intro z
  obtain ⟨m, hm⟩ := P.mkQ_surjective z.1
  let x : idempotentCoordinate (k := k) e M :=
    ⟨(MulOpposite.op e) • m, ⟨m, rfl⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change P.mkQ ((MulOpposite.op e) • m) = z.1
  rw [P.mkQ.map_smul, hm]
  exact idempotentCoordinate_fixed he (quotientFGObj M P) z

/-- Taking an idempotent coordinate preserves the canonical short exact
sequence of a submodule and its quotient. -/
theorem idempotentCoordinate_submodule_quotient_exact
    {e : A} (he : IsIdempotentElem e)
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    Function.Exact
      (idempotentCoordinateSubmoduleLinearMap (k := k) e M P)
      (idempotentCoordinateQuotientLinearMap (k := k) e M P) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    have hxq : P.mkQ x.1 = 0 := by
      have := LinearMap.mem_ker.mp hx
      exact congrArg Subtype.val this
    have hxP : x.1 ∈ P := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxq
      exact hxq
    let p : P := ⟨x.1, hxP⟩
    let y : idempotentCoordinate (k := k) e (submoduleFGObj M P) :=
      ⟨p, ⟨p, by
        apply Subtype.ext
        exact idempotentCoordinate_fixed (k := k) he M x⟩⟩
    exact ⟨y, by
      apply Subtype.ext
      rfl⟩
  · rintro x ⟨y, hy⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    have hval : x.1 = y.1.1 := congrArg Subtype.val hy.symm
    change P.mkQ x.1 = 0
    rw [hval, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact y.1.2

/-- Idempotent-coordinate dimensions add across a submodule and its
quotient.  This is the composition-multiplicity additivity needed when two
isomorphic simple factors occur in different Loewy layers rather than as a
semisimple product subquotient. -/
theorem finrank_idempotentCoordinate_eq_add_submodule_quotient
    {e : A} (he : IsIdempotentElem e)
    (M : FinitelyGeneratedCategory A) (P : Submodule Aᵐᵒᵖ M) :
    Module.finrank k (idempotentCoordinate (k := k) e M) =
      Module.finrank k
        (idempotentCoordinate (k := k) e (submoduleFGObj M P)) +
      Module.finrank k
        (idempotentCoordinate (k := k) e (quotientFGObj M P)) := by
  letI : Module.Finite k M :=
    finite_over_field_of_finitelyGenerated k A M
  letI : Module.Finite k (submoduleFGObj M P) :=
    finite_over_field_of_finitelyGenerated k A (submoduleFGObj M P)
  letI : Module.Finite k (quotientFGObj M P) :=
    finite_over_field_of_finitelyGenerated k A (quotientFGObj M P)
  exact
    MagnitudeConjecture.LinearMap.finrank_eq_add_of_exact_of_injective_of_surjective
      (idempotentCoordinateSubmoduleLinearMap (k := k) e M P)
      (idempotentCoordinateQuotientLinearMap (k := k) e M P)
      (idempotentCoordinate_submodule_quotient_exact (k := k) he M P)
      (idempotentCoordinateSubmoduleLinearMap_injective (k := k) e M P)
      (idempotentCoordinateQuotientLinearMap_surjective (k := k) he M P)

/-- Coordinate thinness passes to finitely generated quotients. -/
theorem IsCoordinateThin.quotient
    {e : ι → A} (he : ∀ i, IsIdempotentElem (e i))
    {M : FinitelyGeneratedCategory A}
    (hM : IsCoordinateThin (k := k) e M)
    (P : Submodule Aᵐᵒᵖ M) :
    IsCoordinateThin (k := k) e (quotientFGObj M P) := by
  intro i
  letI : Module.Finite k M :=
    finite_over_field_of_finitelyGenerated k A M
  exact (LinearMap.finrank_le_finrank_of_surjective
    (idempotentCoordinateQuotientLinearMap_surjective
      (k := k) (he i) M P)).trans (hM i)

/-- The product of two finitely generated right modules, retained as an
object of the finitely generated module category. -/
def prodFGObj
    (M N : FinitelyGeneratedCategory A) :
    FinitelyGeneratedCategory A := by
  letI : Module.Finite Aᵐᵒᵖ (M × N) := inferInstance
  exact FGModuleCat.of Aᵐᵒᵖ (M × N)

/-- An idempotent coordinate of a binary product is the product of the two
idempotent coordinates. -/
def idempotentCoordinateProdLinearEquiv
    (e : A) (M N : FinitelyGeneratedCategory A) :
    idempotentCoordinate (k := k) e (prodFGObj M N) ≃ₗ[k]
      idempotentCoordinate (k := k) e M ×
        idempotentCoordinate (k := k) e N where
  toFun x := by
    refine (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩)
    · obtain ⟨z, hz⟩ := x.2
      change (MulOpposite.op e) • z = x.1 at hz
      exact ⟨z.1, congrArg Prod.fst hz⟩
    · obtain ⟨z, hz⟩ := x.2
      change (MulOpposite.op e) • z = x.1 at hz
      exact ⟨z.2, congrArg Prod.snd hz⟩
  invFun x := by
    refine ⟨(x.1.1, x.2.1), ?_⟩
    obtain ⟨z, hz⟩ := x.1.2
    obtain ⟨w, hw⟩ := x.2.2
    change (MulOpposite.op e) • z = x.1.1 at hz
    change (MulOpposite.op e) • w = x.2.1 at hw
    exact ⟨(z, w), Prod.ext hz hw⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- A module has a repeated self-subquotient when some subquotient is the
product of two copies of a nonzero finitely generated module. -/
def HasRepeatedSelfSubquotient (W : FinitelyGeneratedCategory A) : Prop :=
  ∃ F : FinitelyGeneratedCategory A, Nontrivial F ∧
    ∃ (P : Submodule Aᵐᵒᵖ W)
      (Q : Submodule Aᵐᵒᵖ (submoduleFGObj W P)),
      Nonempty (quotientFGObj (submoduleFGObj W P) Q ≅ prodFGObj F F)

/-- A surjection from `W` onto two copies of a nonzero module is a repeated
self-subquotient certificate. -/
theorem hasRepeatedSelfSubquotient_of_surjective_prod_self
    (W F : FinitelyGeneratedCategory A) [Nontrivial F]
    (q : W →ₗ[Aᵐᵒᵖ] (F × F)) (hq : Function.Surjective q) :
    HasRepeatedSelfSubquotient W := by
  let P : Submodule Aᵐᵒᵖ W := ⊤
  let qTop : P →ₗ[Aᵐᵒᵖ] (F × F) := q.domRestrict P
  have hqTop : Function.Surjective qTop := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    exact ⟨⟨x, Submodule.mem_top⟩, hx⟩
  refine ⟨F, inferInstance, P, qTop.ker, ?_⟩
  exact ⟨
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ (qTop.quotKerEquivOfSurjective hqTop)⟩

/-- A submodule which is linearly equivalent to two copies of one nonzero
module is already a repeated self-subquotient certificate. -/
theorem hasRepeatedSelfSubquotient_of_submodule_linearEquiv_prod_self
    (W F : FinitelyGeneratedCategory A) [Nontrivial F]
    (P : Submodule Aᵐᵒᵖ W)
    (eP : P ≃ₗ[Aᵐᵒᵖ] (F × F)) :
    HasRepeatedSelfSubquotient W := by
  let Q : Submodule Aᵐᵒᵖ P := ⊥
  let eBot : (P ⧸ Q) ≃ₗ[Aᵐᵒᵖ] P :=
    (Q.quotientEquivOfIsCompl (⊤ : Submodule Aᵐᵒᵖ P)
      isCompl_bot_top).trans
        (LinearEquiv.ofTop (⊤ : Submodule Aᵐᵒᵖ P) rfl)
  refine ⟨F, inferInstance, P, Q, ?_⟩
  exact ⟨
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ (eBot.trans eP)⟩

/-- Two disjoint isomorphic nonzero submodules form a repeated submodule of
the ambient module. -/
theorem hasRepeatedSelfSubquotient_of_disjoint_isomorphic_submodules
    (W : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ W) [Nontrivial P]
    (hinf : P ⊓ Q = ⊥) (ePQ : P ≃ₗ[Aᵐᵒᵖ] Q) :
    HasRepeatedSelfSubquotient W := by
  let f₀ : (P × Q) →ₗ[Aᵐᵒᵖ] W := P.subtype.coprod Q.subtype
  let f : (P × Q) →ₗ[Aᵐᵒᵖ]
      ↥(P ⊔ Q : Submodule Aᵐᵒᵖ W) :=
    f₀.codRestrict (P ⊔ Q) (fun x ↦ by
      change x.1.1 + x.2.1 ∈ P ⊔ Q
      exact Submodule.add_mem_sup x.1.2 x.2.2)
  have hdisjoint : Disjoint P Q := by
    rw [disjoint_iff]
    exact hinf
  have hdisjointRange :
      Disjoint (LinearMap.range P.subtype) (LinearMap.range Q.subtype) := by
    simpa using hdisjoint
  have hf₀ : Function.Injective f₀ := by
    rw [← LinearMap.ker_eq_bot,
      LinearMap.ker_coprod_of_disjoint_range _ _ hdisjointRange,
      Submodule.ker_subtype, Submodule.ker_subtype, Submodule.prod_bot]
  have hf : Function.Injective f := by
    intro x y hxy
    apply hf₀
    exact congrArg Subtype.val hxy
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp z.2
    refine ⟨(⟨p, hp⟩, ⟨q, hq⟩), ?_⟩
    apply Subtype.ext
    exact hpq
  let eSum : (P × Q) ≃ₗ[Aᵐᵒᵖ]
      ↥(P ⊔ Q : Submodule Aᵐᵒᵖ W) :=
    LinearEquiv.ofBijective f ⟨hf, hfsurj⟩
  let eProd : ↥(P ⊔ Q : Submodule Aᵐᵒᵖ W) ≃ₗ[Aᵐᵒᵖ]
      (P × P) :=
    eSum.symm.trans
      (LinearEquiv.prodCongr (LinearEquiv.refl Aᵐᵒᵖ P) ePQ.symm)
  let F := submoduleFGObj W P
  letI : Nontrivial F := ‹Nontrivial P›
  exact hasRepeatedSelfSubquotient_of_submodule_linearEquiv_prod_self
    W F (P ⊔ Q) eProd

/-- A submodule which surjects onto two copies of one nonzero module gives a
repeated self-subquotient of the ambient module. -/
theorem hasRepeatedSelfSubquotient_of_submodule_surjective_prod_self
    (W F : FinitelyGeneratedCategory A) [Nontrivial F]
    (P : Submodule Aᵐᵒᵖ W)
    (q : P →ₗ[Aᵐᵒᵖ] (F × F)) (hq : Function.Surjective q) :
    HasRepeatedSelfSubquotient W := by
  refine ⟨F, inferInstance, P, q.ker, ?_⟩
  exact ⟨
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ (q.quotKerEquivOfSurjective hq)⟩

/-- A submodule consisting of two copies of a nonzero module inside a
quotient of `W` gives a repeated self-subquotient of `W`.  The witnessing
submodule is pulled back along the quotient map and then divided by the
kernel of the restricted surjection. -/
theorem hasRepeatedSelfSubquotient_of_quotient_submodule_prod_self
    (W F : FinitelyGeneratedCategory A) [Nontrivial F]
    (Q₀ : Submodule Aᵐᵒᵖ W)
    (T : Submodule Aᵐᵒᵖ (quotientFGObj W Q₀))
    (hT : T ≃ₗ[Aᵐᵒᵖ] (F × F)) :
    HasRepeatedSelfSubquotient W := by
  let P : Submodule Aᵐᵒᵖ W := T.comap Q₀.mkQ
  let q : P →ₗ[Aᵐᵒᵖ] T :=
    (Q₀.mkQ.domRestrict P).codRestrict T (fun x ↦ x.2)
  have hq : Function.Surjective q := by
    intro t
    obtain ⟨w, hw⟩ := Q₀.mkQ_surjective t.1
    let p : P := ⟨w, by
      change Q₀.mkQ w ∈ T
      rw [hw]
      exact t.2⟩
    refine ⟨p, Subtype.ext ?_⟩
    exact hw
  refine ⟨F, inferInstance, P, q.ker, ?_⟩
  exact ⟨
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ ((q.quotKerEquivOfSurjective hq).trans hT)⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Coordinate dimensions add under binary products. -/
theorem finrank_idempotentCoordinate_prod
    (e : A) (M N : FinitelyGeneratedCategory A) :
    Module.finrank k (idempotentCoordinate (k := k) e (prodFGObj M N)) =
      Module.finrank k (idempotentCoordinate (k := k) e M) +
        Module.finrank k (idempotentCoordinate (k := k) e N) := by
  letI : Module.Finite k M :=
    finite_over_field_of_finitelyGenerated k A M
  letI : Module.Finite k N :=
    finite_over_field_of_finitelyGenerated k A N
  rw [(idempotentCoordinateProdLinearEquiv (k := k) e M N).finrank_eq,
    Module.finrank_prod]

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Two copies of a module with a nonzero chosen coordinate cannot form a
coordinate-thin product. -/
theorem not_coordinateThin_prod_self_of_coordinate_nonzero
    (e : ι → A) (M : FinitelyGeneratedCategory A)
    (i : ι)
    (hi : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) M)) :
    ¬ IsCoordinateThin (k := k) e (prodFGObj M M) := by
  intro hthin
  have hle := hthin i
  rw [finrank_idempotentCoordinate_prod (k := k)] at hle
  omega

/-- A module is not coordinate-thin if one of its subquotients is two copies
of a module having a nonzero coordinate.  This is the reusable contradiction
form for the repeated-simple-factor obstruction modules in the biseriality
induction. -/
theorem not_coordinateThin_of_subquotient_prod_self
    (e : ι → A) (he : ∀ i, IsIdempotentElem (e i))
    (W F : FinitelyGeneratedCategory A)
    (P : Submodule Aᵐᵒᵖ W)
    (Q : Submodule Aᵐᵒᵖ (submoduleFGObj W P))
    (f : quotientFGObj (submoduleFGObj W P) Q ≅ prodFGObj F F)
    (i : ι)
    (hi : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) F)) :
    ¬ IsCoordinateThin (k := k) e W := by
  intro hW
  have hP : IsCoordinateThin (k := k) e (submoduleFGObj W P) :=
    hW.submodule P
  have hQ : IsCoordinateThin (k := k) e
      (quotientFGObj (submoduleFGObj W P) Q) :=
    hP.quotient he Q
  have hprod : IsCoordinateThin (k := k) e (prodFGObj F F) :=
    IsCoordinateThin.congr e he f hQ
  exact not_coordinateThin_prod_self_of_coordinate_nonzero
    (k := k) e F i hi hprod

/-- A nonzero module has a nonzero coordinate for some member of a complete
orthogonal idempotent family. -/
theorem exists_positive_idempotentCoordinate
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (M : FinitelyGeneratedCategory A) [Nontrivial M] :
    ∃ i : ι, 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) M) := by
  by_contra h
  push Not at h
  have hzero (i : ι) :
      Module.finrank k (idempotentCoordinate (k := k) (e i) M) = 0 :=
    Nat.eq_zero_of_le_zero (h i)
  have hact (i : ι) (x : M) : (MulOpposite.op (e i)) • x = 0 :=
    (finrank_idempotentCoordinate_eq_zero_iff (k := k)
      (hall.idem i) M).1 (hzero i) x
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  apply hx
  calc
    x = (MulOpposite.op (1 : A)) • x := by simp
    _ = (MulOpposite.op (∑ i : ι, e i)) • x := by rw [hall.complete]
    _ = ∑ i : ι, (MulOpposite.op (e i)) • x := by
      rw [show MulOpposite.op (∑ i : ι, e i) =
          ∑ i : ι, MulOpposite.op (e i) by simp,
        Finset.sum_smul]
    _ = 0 := Finset.sum_eq_zero fun i _ ↦ hact i x

/-- In a coordinate-thin module, no nonzero submodule of the radical is
isomorphic to the top.  The submodule contributes a positive coordinate to
the radical, the isomorphic top contributes the same positive coordinate to
the quotient, and coordinate additivity would make the ambient coordinate
at least two-dimensional. -/
theorem nonisomorphic_submodule_and_top_of_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (M : FinitelyGeneratedCategory A)
    (hM : IsCoordinateThin (k := k) e M)
    (P : Submodule Aᵐᵒᵖ M)
    (hPne : P ≠ ⊥)
    (hPJ : P ≤ Module.jacobson Aᵐᵒᵖ M) :
    ¬ Nonempty
      (P ≃ₗ[Aᵐᵒᵖ] (M ⧸ Module.jacobson Aᵐᵒᵖ M)) := by
  let R := Aᵐᵒᵖ
  let J : Submodule R M := Module.jacobson R M
  letI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hPne
  letI : Nontrivial (submoduleFGObj M P) := ‹Nontrivial P›
  rintro ⟨ePTop⟩
  obtain ⟨i, hiP⟩ := exists_positive_idempotentCoordinate
    (k := k) e hall (submoduleFGObj M P)
  let pToJ : P →ₗ[R] J :=
    P.subtype.codRestrict J (fun p ↦ hPJ p.2)
  let coordPToJ :
      idempotentCoordinate (k := k) (e i) (submoduleFGObj M P) →ₗ[k]
        idempotentCoordinate (k := k) (e i) (submoduleFGObj M J) := {
    toFun x := by
      let y : J := pToJ x.1
      refine ⟨y, ⟨y, ?_⟩⟩
      apply Subtype.ext
      change (MulOpposite.op (e i)) • (x.1.1 : M) = x.1.1
      exact congrArg Subtype.val
        (idempotentCoordinate_fixed (k := k) (hall.idem i)
          (submoduleFGObj M P) x)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hcoordPToJ : Function.Injective coordPToJ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : idempotentCoordinate (k := k) (e i) (submoduleFGObj M J) ↦
        (z.1.1 : M)) hxy
  letI : Module.Finite k (submoduleFGObj M P) :=
    finite_over_field_of_finitelyGenerated k A (submoduleFGObj M P)
  letI : Module.Finite k (submoduleFGObj M J) :=
    finite_over_field_of_finitelyGenerated k A (submoduleFGObj M J)
  have hiJ : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj M J)) := by
    exact hiP.trans_le
      (LinearMap.finrank_le_finrank_of_injective hcoordPToJ)
  let ePTopIso : submoduleFGObj M P ≅ quotientFGObj M J :=
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      R ePTop
  have hcoordEq : Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj M P)) =
      Module.finrank k
        (idempotentCoordinate (k := k) (e i) (quotientFGObj M J)) :=
    (idempotentCoordinateLinearEquivOfIso
      (k := k) (hall.idem i) ePTopIso).finrank_eq
  have hiTop : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) (quotientFGObj M J)) := by
    rwa [← hcoordEq]
  have hdim := finrank_idempotentCoordinate_eq_add_submodule_quotient
    (k := k) (hall.idem i) M J
  have hthin := hM i
  rw [hdim] at hthin
  omega

/-- A nonzero map out of a simple-top module makes every nonzero coordinate
of the source top occur in the target.  The kernel is proper, hence lies in
the source radical, so the source top is a quotient of the image. -/
theorem idempotentCoordinate_pos_of_nonzero_linearMap_of_simpleTop
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (M : FinitelyGeneratedCategory A)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (N : FinitelyGeneratedCategory A)
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : f ≠ 0)
    (i : ι)
    (hiTop : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i)
        (quotientFGObj M (Module.jacobson Aᵐᵒᵖ M)))) :
    0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) N) := by
  let R := Aᵐᵒᵖ
  let J : Submodule R M := Module.jacobson R M
  have hkerNeTop : f.ker ≠ ⊤ := by
    intro hker
    exact hf (LinearMap.ker_eq_top.mp hker)
  have hJcoatom : IsCoatom J := isSimpleModule_iff_isCoatom.mp htop
  obtain ⟨Q, hQcoatom, hkerQ⟩ :=
    (eq_top_or_exists_le_coatom f.ker).resolve_left hkerNeTop
  have hJQ : J ≤ Q := sInf_le hQcoatom
  have hJQeq : J = Q := by
    by_cases hEq : J = Q
    · exact hEq
    have hlt : J < Q := lt_of_le_of_ne hJQ hEq
    exact (hQcoatom.ne_top (hJcoatom.2 _ hlt)).elim
  have hkerJ : f.ker ≤ J := by
    rw [hJQeq]
    exact hkerQ
  let Top : FinitelyGeneratedCategory A := quotientFGObj M J
  let KerQuot : FinitelyGeneratedCategory A := quotientFGObj M f.ker
  let Range : FinitelyGeneratedCategory A := submoduleFGObj N f.range
  let qKerTop : KerQuot →ₗ[R] Top :=
    quotientFGMapQ M f.ker J hkerJ
  have hqKerTop : Function.Surjective qKerTop :=
    quotientFGMapQ_surjective M f.ker J hkerJ
  have hiKerQuot : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) KerQuot) := by
    let qCoord := idempotentCoordinateLinearMap (k := k) (e i) qKerTop
    have hqCoord : Function.Surjective qCoord :=
      idempotentCoordinateLinearMap_surjective
        (k := k) (hall.idem i) qKerTop hqKerTop
    letI : Module.Finite k KerQuot :=
      finite_over_field_of_finitelyGenerated k A KerQuot
    exact hiTop.trans_le
      (LinearMap.finrank_le_finrank_of_surjective hqCoord)
  let eKerRange : KerQuot ≃ₗ[R] f.range := f.quotKerEquivRange
  let eKerRangeIso : KerQuot ≅ Range :=
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      R eKerRange
  have hiRange : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) Range) := by
    rw [← (idempotentCoordinateLinearEquivOfIso
      (k := k) (hall.idem i) eKerRangeIso).finrank_eq]
    exact hiKerQuot
  letI : Module.Finite k Range :=
    finite_over_field_of_finitelyGenerated k A Range
  letI : Module.Finite k N :=
    finite_over_field_of_finitelyGenerated k A N
  exact hiRange.trans_le
    (LinearMap.finrank_le_finrank_of_injective
      (idempotentCoordinateSubmoduleLinearMap_injective
        (k := k) (e i) N f.range))

/-- If a binary product is coordinate-thin, a simple-top module cannot map
nontrivially to both factors.  The same nonzero coordinate of the source top
would occur in both factors and hence twice in their product. -/
theorem linearMap_eq_zero_or_eq_zero_of_coordinateThin_prod_of_simpleTop
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (M N : FinitelyGeneratedCategory A)
    (hprod : IsCoordinateThin (k := k) e (prodFGObj M N))
    (E : FinitelyGeneratedCategory A)
    (hEtop : IsSimpleModule Aᵐᵒᵖ
      (E ⧸ Module.jacobson Aᵐᵒᵖ E))
    (f : E →ₗ[Aᵐᵒᵖ] M) (g : E →ₗ[Aᵐᵒᵖ] N) :
    f = 0 ∨ g = 0 := by
  by_contra hfg
  push Not at hfg
  let Top : FinitelyGeneratedCategory A :=
    quotientFGObj E (Module.jacobson Aᵐᵒᵖ E)
  letI : Nontrivial Top := hEtop.nontrivial
  obtain ⟨i, hiTop⟩ := exists_positive_idempotentCoordinate
    (k := k) e hall Top
  have hiM : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) M) :=
    idempotentCoordinate_pos_of_nonzero_linearMap_of_simpleTop
      e hall E hEtop M f hfg.1 i hiTop
  have hiN : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) N) :=
    idempotentCoordinate_pos_of_nonzero_linearMap_of_simpleTop
      e hall E hEtop N g hfg.2 i hiTop
  have hthin := hprod i
  rw [finrank_idempotentCoordinate_prod (k := k)] at hthin
  omega

/-- In a coordinate-thin simple-top module, every map to a subquotient of a
module embedded in its Jacobson radical is zero.  A nonzero map would make a
coordinate of the source top occur again inside the radical. -/
theorem linearMap_to_injective_jacobson_subquotient_eq_zero_of_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (M : FinitelyGeneratedCategory A)
    (hM : IsCoordinateThin (k := k) e M)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (E : FinitelyGeneratedCategory A)
    (j : E →ₗ[Aᵐᵒᵖ] M) (hj : Function.Injective j)
    (hjJ : j.range ≤ Module.jacobson Aᵐᵒᵖ M)
    (K : Submodule Aᵐᵒᵖ E)
    (f : M →ₗ[Aᵐᵒᵖ] quotientFGObj E K) :
    f = 0 := by
  let R := Aᵐᵒᵖ
  let J : Submodule R M := Module.jacobson R M
  let Top : FinitelyGeneratedCategory A := quotientFGObj M J
  let Target : FinitelyGeneratedCategory A :=
    quotientFGObj E K
  by_contra hf
  have hkerNeTop : f.ker ≠ ⊤ := by
    intro hker
    exact hf (LinearMap.ker_eq_top.mp hker)
  have hJcoatom : IsCoatom J := isSimpleModule_iff_isCoatom.mp htop
  obtain ⟨Q, hQcoatom, hkerQ⟩ :=
    (eq_top_or_exists_le_coatom f.ker).resolve_left hkerNeTop
  have hJQ : J ≤ Q := sInf_le hQcoatom
  have hJQeq : J = Q := by
    by_cases hEq : J = Q
    · exact hEq
    have hlt : J < Q := lt_of_le_of_ne hJQ hEq
    exact (hQcoatom.ne_top (hJcoatom.2 _ hlt)).elim
  have hkerJ : f.ker ≤ J := by
    rw [hJQeq]
    exact hkerQ
  let KerQuot : FinitelyGeneratedCategory A := quotientFGObj M f.ker
  let Range : FinitelyGeneratedCategory A := submoduleFGObj Target f.range
  letI : Nontrivial Top := htop.nontrivial
  obtain ⟨i, hiTop⟩ := exists_positive_idempotentCoordinate
    (k := k) e hall Top
  let qKerTop : KerQuot →ₗ[R] Top :=
    quotientFGMapQ M f.ker J hkerJ
  have hqKerTop : Function.Surjective qKerTop :=
    quotientFGMapQ_surjective M f.ker J hkerJ
  have hiKerQuot : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) KerQuot) := by
    let qCoord := idempotentCoordinateLinearMap (k := k) (e i) qKerTop
    have hqCoord : Function.Surjective qCoord :=
      idempotentCoordinateLinearMap_surjective
        (k := k) (hall.idem i) qKerTop hqKerTop
    letI : Module.Finite k KerQuot :=
      finite_over_field_of_finitelyGenerated k A KerQuot
    exact hiTop.trans_le
      (LinearMap.finrank_le_finrank_of_surjective hqCoord)
  let eKerRange : KerQuot ≃ₗ[R] f.range := f.quotKerEquivRange
  let eKerRangeIso : KerQuot ≅ Range :=
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      R eKerRange
  have hiRange : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) Range) := by
    rw [← (idempotentCoordinateLinearEquivOfIso
      (k := k) (hall.idem i) eKerRangeIso).finrank_eq]
    exact hiKerQuot
  have hiTarget : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) Target) := by
    letI : Module.Finite k Range :=
      finite_over_field_of_finitelyGenerated k A Range
    letI : Module.Finite k Target :=
      finite_over_field_of_finitelyGenerated k A Target
    exact hiRange.trans_le
      (LinearMap.finrank_le_finrank_of_injective
        (idempotentCoordinateSubmoduleLinearMap_injective
          (k := k) (e i) Target f.range))
  let qETarget : E →ₗ[R] Target :=
    quotientFGMkQ E K
  have hqETarget : Function.Surjective qETarget :=
    quotientFGMkQ_surjective E K
  let qECoord := idempotentCoordinateLinearMap (k := k) (e i) qETarget
  have hqECoord : Function.Surjective qECoord :=
    idempotentCoordinateLinearMap_surjective
      (k := k) (hall.idem i) qETarget hqETarget
  letI : Module.Finite k E :=
    finite_over_field_of_finitelyGenerated k A E
  letI : Module.Finite k Target :=
    finite_over_field_of_finitelyGenerated k A Target
  have hiE : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) E) :=
    hiTarget.trans_le
      (LinearMap.finrank_le_finrank_of_surjective hqECoord)
  let eToJ : E →ₗ[R] J :=
    j.codRestrict J (fun x ↦ hjJ ⟨x, rfl⟩)
  let coordEToJ :
      idempotentCoordinate (k := k) (e i) E →ₗ[k]
        idempotentCoordinate (k := k) (e i) (submoduleFGObj M J) := {
    toFun x := by
      let y : J := eToJ x.1
      refine ⟨y, ⟨y, ?_⟩⟩
      apply Subtype.ext
      change (MulOpposite.op (e i)) • j x.1 = j x.1
      rw [← map_smul]
      exact congrArg j
        (idempotentCoordinate_fixed (k := k) (hall.idem i)
          E x)
    map_add' x y := by
      apply Subtype.ext
      exact eToJ.map_add x.1 y.1
    map_smul' c x := by
      apply Subtype.ext
      exact eToJ.map_smul_of_tower c x.1 }
  have hcoordEToJ : Function.Injective coordEToJ := by
    intro x y hxy
    apply Subtype.ext
    apply hj
    exact congrArg
      (fun z : idempotentCoordinate (k := k) (e i)
          (submoduleFGObj M J) ↦ (z.1.1 : M)) hxy
  letI : Module.Finite k (submoduleFGObj M J) :=
    finite_over_field_of_finitelyGenerated k A (submoduleFGObj M J)
  have hiJ : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj M J)) :=
    hiE.trans_le (LinearMap.finrank_le_finrank_of_injective hcoordEToJ)
  have hdim := finrank_idempotentCoordinate_eq_add_submodule_quotient
    (k := k) (hall.idem i) M J
  have hthin := hM i
  rw [hdim] at hthin
  dsimp only [Top] at hiTop
  omega

/-- Submodule form of
`linearMap_to_injective_jacobson_subquotient_eq_zero_of_coordinateThin`. -/
theorem linearMap_to_jacobson_subquotient_eq_zero_of_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (M : FinitelyGeneratedCategory A)
    (hM : IsCoordinateThin (k := k) e M)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (E : Submodule Aᵐᵒᵖ M)
    (hEJ : E ≤ Module.jacobson Aᵐᵒᵖ M)
    (K : Submodule Aᵐᵒᵖ E)
    (f : M →ₗ[Aᵐᵒᵖ] quotientFGObj (submoduleFGObj M E) K) :
    f = 0 := by
  let jE : submoduleFGObj M E →ₗ[Aᵐᵒᵖ] M := {
    toFun := fun (x : submoduleFGObj M E) ↦ x.1
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hjE : Function.Injective jE := by
    intro x y hxy
    exact Subtype.ext hxy
  have hjErange : jE.range = E := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  exact linearMap_to_injective_jacobson_subquotient_eq_zero_of_coordinateThin
    e hall M hM htop (submoduleFGObj M E) jE hjE (by
        rw [hjErange]
        exact hEJ) K f

/-- Over a complete idempotent family, a subquotient consisting of two
copies of any nonzero module is enough to refute coordinate thinness. -/
theorem not_coordinateThin_of_subquotient_prod_self_of_complete
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (W F : FinitelyGeneratedCategory A) [Nontrivial F]
    (P : Submodule Aᵐᵒᵖ W)
    (Q : Submodule Aᵐᵒᵖ (submoduleFGObj W P))
    (f : quotientFGObj (submoduleFGObj W P) Q ≅ prodFGObj F F) :
    ¬ IsCoordinateThin (k := k) e W := by
  obtain ⟨i, hi⟩ := exists_positive_idempotentCoordinate
    (k := k) e hall F
  exact not_coordinateThin_of_subquotient_prod_self
    (k := k) e hall.idem W F P Q f i hi

/-- Under the all-indecomposables-thin premise, no indecomposable module can
have a subquotient consisting of two copies of a nonzero module. -/
theorem no_indec_subquotient_prod_self_of_all_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A) (hW : Indecomposable W)
    (F : FinitelyGeneratedCategory A) [Nontrivial F]
    (P : Submodule Aᵐᵒᵖ W)
    (Q : Submodule Aᵐᵒᵖ (submoduleFGObj W P))
    (f : quotientFGObj (submoduleFGObj W P) Q ≅ prodFGObj F F) :
    False :=
  not_coordinateThin_of_subquotient_prod_self_of_complete
    (k := k) e hall W F P Q f (H W hW)

/-- Complete coordinate thinness forbids repeated self-subquotients in every
indecomposable module. -/
theorem no_repeatedSelfSubquotient_of_all_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A) (hW : Indecomposable W) :
    ¬ HasRepeatedSelfSubquotient W := by
  rintro ⟨F, hF, P, Q, ⟨f⟩⟩
  letI : Nontrivial F := hF
  exact no_indec_subquotient_prod_self_of_all_coordinateThin
    (k := k) e hall H W hW F P Q f

end MagnitudeConjecture.RightModule
