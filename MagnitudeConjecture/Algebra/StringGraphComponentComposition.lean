import MagnitudeConjecture.Algebra.StringGraphComponentEndomorphism

/-!
# Composition of string coefficient-component maps

Composition is matrix multiplication in the position bases.  This file
records that formula at the coefficient level and specializes it to the
component-indicator basis.  It is the algebraic interface for the remaining
proper-overlap nilpotence argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

noncomputable local instance positionAtFintype
    (C : Word R) (x : Q) : Fintype (C.PositionAt x) :=
  Fintype.ofFinite _

/-- Coefficients of a composite are obtained by summing over the intermediate
word positions above the displayed vertex. -/
theorem morphismCoefficient_comp
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (g : D.rightModule hD ⟶ E.rightModule hE)
    {x : Q} (i : C.PositionAt x) (l : E.PositionAt x) :
    C.morphismCoefficient E hC hE (f ≫ g) i l =
      ∑ j : D.PositionAt x,
        C.morphismCoefficient D hC hD f i j *
          D.morphismCoefficient E hD hE g j l := by
  classical
  let F : C.Space x →ₗ[k] D.Space x :=
    (f.app (Opposite.op (obj R x))).hom
  let G : D.Space x →ₗ[k] E.Space x :=
    (g.app (Opposite.op (obj R x))).hom
  let H : D.Space x →ₗ[k] k := (Finsupp.lapply l).comp G
  have hdecomp :
      F (Finsupp.single i 1) =
        ∑ j : D.PositionAt x,
          (F (Finsupp.single i 1) j) • Finsupp.single j 1 := by
    apply Finsupp.ext
    intro j
    simp
  change H (F (Finsupp.single i 1)) = _
  rw [hdecomp, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- The position-indexed form of the coefficient composition formula. -/
theorem morphismCoefficientAt_comp
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (g : D.rightModule hD ⟶ E.rightModule hE)
    (p : C.MorphismCoefficientPosition E) :
    C.morphismCoefficientAt E hC hE (f ≫ g) p =
      ∑ j : D.PositionAt p.1,
        C.morphismCoefficientAt D hC hD f ⟨p.1, p.2.1, j⟩ *
          D.morphismCoefficientAt E hD hE g ⟨p.1, j, p.2.2⟩ := by
  rcases p with ⟨x, i, l⟩
  exact C.morphismCoefficient_comp D E hC hD hE f g i l

/-- Composition of two graph-component basis maps is the convolution of
their zero-one component indicators over intermediate word positions. -/
theorem morphismCoefficientAt_boundaryFreeComponentMap_comp
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (p : C.MorphismCoefficientPosition E) :
    C.morphismCoefficientAt E hC hE
        (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
          D.boundaryFreeMorphismCoefficientComponentMap E hD hE second) p =
      ∑ j : D.PositionAt p.1,
        C.coefficientComponentIndicator D first.1.representative
            ⟨p.1, p.2.1, j⟩ *
          D.coefficientComponentIndicator E second.1.representative
            ⟨p.1, j, p.2.2⟩ := by
  rw [C.morphismCoefficientAt_comp D E hC hD hE]
  apply Finset.sum_congr rfl
  intro j _
  rw [C.morphismCoefficientAt_boundaryFreeComponentMap,
    D.morphismCoefficientAt_boundaryFreeComponentMap]

/-- The structure coefficient of the product of two graph-component basis
maps in a third graph-component basis direction. -/
def boundaryFreeMorphismCoefficientComponentCompositionCoefficient
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (output : C.BoundaryFreeMorphismCoefficientComponent E) : k :=
  C.morphismCoefficientAt E hC hE
    (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
      D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
    output.1.representative

/-- A structure coefficient counts, in the coefficient field, intermediate
positions simultaneously supported by the two component relations. -/
theorem boundaryFreeMorphismCoefficientComponentCompositionCoefficient_eq
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (output : C.BoundaryFreeMorphismCoefficientComponent E) :
    C.boundaryFreeMorphismCoefficientComponentCompositionCoefficient
        D E hC hD hE first second output =
      ∑ j : D.PositionAt output.1.representative.1,
        C.coefficientComponentIndicator D first.1.representative
            ⟨output.1.representative.1,
              output.1.representative.2.1, j⟩ *
          D.coefficientComponentIndicator E second.1.representative
            ⟨output.1.representative.1,
              j, output.1.representative.2.2⟩ := by
  exact C.morphismCoefficientAt_boundaryFreeComponentMap_comp
    D E hC hD hE first second output.1.representative

/-- The graph-component multiplication table reconstructs the composite of
two basis maps. -/
theorem boundaryFreeMorphismCoefficientComponentMap_comp_eq_sum
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E) :
    C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second =
      ∑ output : C.BoundaryFreeMorphismCoefficientComponent E,
        C.boundaryFreeMorphismCoefficientComponentCompositionCoefficient
            D E hC hD hE first second output •
          C.boundaryFreeMorphismCoefficientComponentMap E hC hE output := by
  classical
  let b := C.boundaryFreeMorphismCoefficientBasis E hC hE
  let product :=
    C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
      D.boundaryFreeMorphismCoefficientComponentMap E hD hE second
  calc
    product = ∑ output, b.repr product output • b output :=
      (b.sum_repr product).symm
    _ = ∑ output,
        C.boundaryFreeMorphismCoefficientComponentCompositionCoefficient
            D E hC hD hE first second output •
          C.boundaryFreeMorphismCoefficientComponentMap E hC hE output := by
      apply Finset.sum_congr rfl
      intro output _
      rw [C.boundaryFreeMorphismCoefficientBasis_repr_apply]
      simp only [b, boundaryFreeMorphismCoefficientBasis,
        Module.Basis.coe_mk, product,
        boundaryFreeMorphismCoefficientComponentCompositionCoefficient]

end MagnitudeConjecture.BoundQuiver.StringWord.Word
