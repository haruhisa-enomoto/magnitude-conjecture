import MagnitudeConjecture.Algebra.StatementTheorem

universe u

/-- Magnitude is bounded below by the number of simple right-module classes,
with equality exactly for special biserial algebras. -/
theorem MagnitudeConjecture.magnitudeTheorem
    (k A : Type u) [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] : MagnitudeConjecture.Statement.MainClaim k A :=
  MagnitudeConjecture.Statement.mainClaim
