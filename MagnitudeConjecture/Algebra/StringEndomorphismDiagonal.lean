import MagnitudeConjecture.Algebra.StringMorphismSupport

/-!
# Diagonal coefficients of string-module endomorphisms

Naturality makes the diagonal coefficient of any endomorphism constant along
the complete word, including when displayed vertices repeat.  The source
position also shows directly that every literal string representation is a
nonzero object.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The diagonal coefficient of a natural endomorphism at a position basis
vector. -/
def endomorphismCoefficient (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono)
    {x : Q} (i : C.PositionAt x) : k :=
  C.morphismCoefficient C hmono hmono f i i

theorem endomorphismCoefficient_eq_of_arrowStep
    (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    C.endomorphismCoefficient hmono f i =
      C.endomorphismCoefficient hmono f j := by
  exact C.morphismCoefficient_eq_of_arrowSteps C hmono hmono f
    a i j i j hij hij

/-- The diagonal coefficient of an endomorphism is constant along every
string word, including words with repeated displayed vertices. -/
theorem endomorphismCoefficient_eq_source
    (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono)
    {x : Q} (i : C.PositionAt x) :
    C.endomorphismCoefficient hmono f i =
      C.endomorphismCoefficient hmono f C.sourcePosition := by
  change C.morphismCoefficientAt C hmono hmono f
      (C.diagonalMorphismCoefficientPosition i) =
    C.morphismCoefficientAt C hmono hmono f
      (C.diagonalMorphismCoefficientPosition C.sourcePosition)
  exact C.morphismCoefficientAt_eq_of_eqvGen C hmono hmono f
    (C.diagonalMorphismCoefficientPosition_eqvGen_source i)

/-- Every string representation is a nonzero object of the raw functor
category. -/
theorem rightModule_not_isZero
    (C : Word R) (hmono : IsMonomial R) :
    ¬ IsZero (C.rightModule hmono) := by
  intro hzero
  have hid : 𝟙 (C.rightModule hmono) = 0 :=
    (IsZero.iff_id_eq_zero (C.rightModule hmono)).1 hzero
  have happ := congrArg
    (fun eta : C.rightModule hmono ⟶ C.rightModule hmono =>
      eta.app (Opposite.op (obj R C.source))) hid
  have hlinear := congrArg ModuleCat.Hom.hom happ
  have hvalue := LinearMap.congr_fun hlinear
    (Finsupp.single C.sourcePosition 1)
  change Finsupp.single C.sourcePosition 1 =
    (0 : C.Space C.source) at hvalue
  have hcoord := congrArg
    (fun v : C.Space C.source => v C.sourcePosition) hvalue
  have hone : (1 : k) = 0 := by
    simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hcoord
  exact one_ne_zero hone

end MagnitudeConjecture.BoundQuiver.StringWord.Word
