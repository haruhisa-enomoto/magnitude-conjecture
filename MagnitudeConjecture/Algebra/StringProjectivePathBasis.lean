import MagnitudeConjecture.Algebra.StringArrowRightIdealAction

/-!
# Path bases of represented string projectives

For a displayed vertex of a string presentation, the nontrivial surviving
paths ending at that vertex split uniquely according to their final quiver
arrow.  This file packages that path partition as the direct sum of the
represented string-arrow modules inside the corresponding canonical
projective.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

instance representedVertexModuleKModule
    (P : StringPresentation k A Q) (y : Q) :
    Module k (P.representedVertexModule y) :=
  Module.restrictScalars k P.quotientCategoryAlgebraᵐᵒᵖ _

instance representedVertexModuleIsScalarTower
    (P : StringPresentation k A Q) (y : Q) :
    IsScalarTower k P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) :=
  IsScalarTower.restrictScalars k P.quotientCategoryAlgebraᵐᵒᵖ _

/-- The coefficient-field structure obtained by restricting the category-
algebra action agrees with the native coefficient-field structure on the
represented Hom space. -/
def representedVertexKLinearEquiv
    (P : StringPresentation k A Q) (y : Q) :
    P.representedVertexModule y ≃ₗ[k] P.representedVertexHom y where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r f := by
    let fk : P.representedVertexHom y := f
    have hscalar :
        r • fk =
          (algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ r) • f := by
      change r • fk = (r • 𝟙 _) ≫ fk
      simp
    exact hscalar.symm

/-- Vertex coordinates as a coefficient-field linear equivalence on the
represented category-algebra module. -/
def representedVertexPathCoordinateLinearEquiv
    (P : StringPresentation k A Q) (y : Q) :
    P.representedVertexModule y ≃ₗ[k]
      (∀ X : Category P.toPresentation.relations,
        obj P.toPresentation.relations y ⟶ X) :=
  (P.representedVertexKLinearEquiv y).trans
    (P.representedVertexCoordinateLinearEquiv y)

/-- Displayed quiver arrows ending at a fixed vertex. -/
abbrev DisplayedIncomingArrow (y : Q) := Σ x : Q, x ⟶ y

/-- All surviving paths ending at a fixed displayed vertex, with their
starting vertex retained. -/
abbrev VertexPath (P : StringPresentation k A Q) (y : Q) :=
  Σ z : Q, SurvivingPath P.toPresentation.relations z y

/-- The surviving paths ending at a vertex form a finite type. -/
instance vertexPathFinite (P : StringPresentation k A Q) (y : Q) :
    Finite (P.VertexPath y) := by
  letI (z : Q) : Finite
      (SurvivingPath P.toPresentation.relations z y) :=
    survivingPathFiniteOfAdmissible P.toPresentation.relations
      P.toPresentation.admissible z y
  infer_instance

/-- The monomial path basis in a coordinate indexed by an arbitrary object
of the quotient path category. -/
def survivingPathBasisObj
    (P : StringPresentation k A Q) (y : Q)
    (X : Category P.toPresentation.relations) :
    Module.Basis
      (SurvivingPath P.toPresentation.relations
        (P.quotientObjectEquiv X) y) k
      (obj P.toPresentation.relations y ⟶ X) := by
  rcases X with ⟨z⟩
  exact survivingPathBasis P.toPresentation.relations P.monomial z y

@[simp]
theorem survivingPathBasisObj_obj
    (P : StringPresentation k A Q) (y z : Q) :
    P.survivingPathBasisObj y (obj P.toPresentation.relations z) =
      survivingPathBasis P.toPresentation.relations P.monomial z y :=
  rfl

/-- Reindex the small family of path-basis indices from quotient-category
objects to displayed vertices. -/
def vertexPathObjectSigmaEquiv
    (P : StringPresentation k A Q) (y : Q) :
    (Σ X : Category P.toPresentation.relations,
      SurvivingPath P.toPresentation.relations
        (P.quotientObjectEquiv X) y) ≃ P.VertexPath y where
  toFun p := ⟨P.quotientObjectEquiv p.1, p.2⟩
  invFun p := ⟨obj P.toPresentation.relations p.1, p.2⟩
  left_inv p := by
    rcases p with ⟨⟨z⟩, p⟩
    rfl
  right_inv p := by
    rcases p with ⟨z, p⟩
    rfl

@[simp]
theorem vertexPathObjectSigmaEquiv_symm_apply
    (P : StringPresentation k A Q) (y : Q) (p : P.VertexPath y) :
    (P.vertexPathObjectSigmaEquiv y).symm p =
      ⟨obj P.toPresentation.relations p.1, p.2⟩ :=
  by
    rcases p with ⟨z, p⟩
    rfl

/-- Vertex coordinates and the monomial path bases give the global path
basis of a represented canonical projective. -/
def representedVertexPathBasis (P : StringPresentation k A Q) (y : Q) :
    Module.Basis (P.VertexPath y) k (P.representedVertexModule y) :=
  ((Pi.basis fun X : Category P.toPresentation.relations ↦
      P.survivingPathBasisObj y X).map
    (P.representedVertexPathCoordinateLinearEquiv y).symm).reindex
      (P.vertexPathObjectSigmaEquiv y)

/-- In its starting-object coordinate, a global path-basis vector is the
corresponding pointwise monomial path-basis vector. -/
theorem representedVertexPathBasis_coordinate_self
    (P : StringPresentation k A Q) (y : Q) (p : P.VertexPath y) :
    P.representedVertexPathCoordinateLinearEquiv y
        (P.representedVertexPathBasis y p)
          (obj P.toPresentation.relations p.1) =
      survivingPathBasis P.toPresentation.relations P.monomial p.1 y p.2 := by
  classical
  rcases p with ⟨z, p⟩
  rw [representedVertexPathBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    P.vertexPathObjectSigmaEquiv_symm_apply]
  exact Pi.single_eq_same _ _

/-- A global path-basis vector vanishes in every other displayed starting
object coordinate. -/
theorem representedVertexPathBasis_coordinate_ne
    (P : StringPresentation k A Q) (y : Q) (p : P.VertexPath y)
    (z : Q) (hz : z ≠ p.1) :
    P.representedVertexPathCoordinateLinearEquiv y
        (P.representedVertexPathBasis y p)
          (obj P.toPresentation.relations z) = 0 := by
  classical
  rw [representedVertexPathBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    P.vertexPathObjectSigmaEquiv_symm_apply]
  apply Pi.single_eq_of_ne
  intro h
  apply hz
  simpa using congrArg P.quotientObjectEquiv h

/-- A surviving path, viewed as the corresponding matrix-supported vector
in the represented canonical projective. -/
def representedPathElement (P : StringPresentation k A Q) (y : Q)
    (p : P.VertexPath y) : P.representedVertexModule y :=
  biproduct.π P.quotientRepresentable
      (obj P.toPresentation.relations p.1) ≫
    P.pathRepresentableMap p.2.1

/-- At its starting vertex, a represented path element has its literal path
coordinate. -/
theorem representedPathElement_coordinate_self
    (P : StringPresentation k A Q) (y : Q) (p : P.VertexPath y) :
    P.representedVertexPathCoordinateLinearEquiv y
      (P.representedPathElement y p)
          (obj P.toPresentation.relations p.1) =
      pathMap P.toPresentation.relations p.2.1 := by
  have hrestrict :
      biproduct.ι P.quotientRepresentable
          (obj P.toPresentation.relations p.1) ≫
        P.representedVertexKLinearEquiv y
          (P.representedPathElement y p) =
        P.pathRepresentableMap p.2.1 := by
    change
      biproduct.ι P.quotientRepresentable
          (obj P.toPresentation.relations p.1) ≫
        (biproduct.π P.quotientRepresentable
          (obj P.toPresentation.relations p.1) ≫
            P.pathRepresentableMap p.2.1) =
        P.pathRepresentableMap p.2.1
    simp
  rw [representedVertexPathCoordinateLinearEquiv,
    LinearEquiv.trans_apply,
    P.representedVertexCoordinateLinearEquiv_apply, hrestrict]
  rfl

/-- A represented path element vanishes in every other starting-vertex
coordinate. -/
theorem representedPathElement_coordinate_ne
    (P : StringPresentation k A Q) (y : Q) (p : P.VertexPath y)
    (z : Q) (hz : z ≠ p.1) :
    P.representedVertexPathCoordinateLinearEquiv y
        (P.representedPathElement y p)
          (obj P.toPresentation.relations z) = 0 := by
  have hobj :
      obj P.toPresentation.relations z ≠
      obj P.toPresentation.relations p.1 := by
    intro h
    apply hz
    simpa using congrArg P.quotientObjectEquiv h
  have hzero :
      biproduct.ι P.quotientRepresentable
          (obj P.toPresentation.relations z) ≫
        P.representedVertexKLinearEquiv y
          (P.representedPathElement y p) = 0 := by
    change
      biproduct.ι P.quotientRepresentable
          (obj P.toPresentation.relations z) ≫
        (biproduct.π P.quotientRepresentable
          (obj P.toPresentation.relations p.1) ≫
            P.pathRepresentableMap p.2.1) = 0
    simp [hobj]
  rw [representedVertexPathCoordinateLinearEquiv,
    LinearEquiv.trans_apply,
    P.representedVertexCoordinateLinearEquiv_apply, hzero]
  rfl

/-- The global represented-projective path basis is the explicit
matrix-supported path family. -/
theorem representedVertexPathBasis_apply
    (P : StringPresentation k A Q) (y : Q) (p : P.VertexPath y) :
    P.representedVertexPathBasis y p = P.representedPathElement y p := by
  classical
  let e := P.representedVertexPathCoordinateLinearEquiv y
  apply e.injective
  funext X
  let z := P.quotientObjectEquiv X
  have hX : X = obj P.toPresentation.relations z := by
    apply P.quotientObjectEquiv.injective
    simp [z]
  rw [hX]
  by_cases hz : z = p.1
  · rw [hz]
    have hb := P.representedVertexPathBasis_coordinate_self y p
    have he := P.representedPathElement_coordinate_self y p
    rw [survivingPathBasis_apply] at hb
    exact hb.trans he.symm
  · have hb := P.representedVertexPathBasis_coordinate_ne y p z hz
    have he := P.representedPathElement_coordinate_ne y p z hz
    exact hb.trans he.symm

end StringPresentation

end MagnitudeConjecture.BoundQuiver
