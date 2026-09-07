import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Surjectivity across a chain of finite-dimensional equivalences
-/

set_option autoImplicit false

namespace LinearMap

universe uK u0 u1 u2 u3 u4 u5

/-- A compact proposition wrapper for linear maps whose injectivity implies
surjectivity.  It is useful when the domain and codomain types are themselves
large categorical expressions. -/
structure SurjectiveOfInjective
    {k : Type uK} [Semiring k]
    {V : Type u0} {W : Type u1}
    [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W]
    (f : V →ₗ[k] W) : Prop where
  out : Function.Injective f → Function.Surjective f

/-- An injective linear map is surjective when its source is
finite-dimensional and its source and target are linearly equivalent. -/
theorem surjective_of_injective_of_equiv
    {k : Type uK} [Field k]
    {V : Type u0} {W : Type u1}
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (e : V ≃ₗ[k] W)
    (hV : FiniteDimensional k V)
    (hf : Function.Injective f) : Function.Surjective f := by
  letI : FiniteDimensional k V := hV
  letI : FiniteDimensional k W := e.finiteDimensional
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    e.finrank_eq).mp hf

/-- An injective linear map is surjective when its source and target are linked
by five linear equivalences and one intermediate space is finite-dimensional.
The equivalences remain separate: this avoids constructing a large nested
`LinearEquiv.trans` term in specialized applications. -/
theorem surjective_of_injective_of_five_equiv
    {k : Type uK} [Field k]
    {V0 : Type u0} {V1 : Type u1} {V2 : Type u2}
    {V3 : Type u3} {V4 : Type u4} {V5 : Type u5}
    [AddCommGroup V0] [Module k V0]
    [AddCommGroup V1] [Module k V1]
    [AddCommGroup V2] [Module k V2]
    [AddCommGroup V3] [Module k V3]
    [AddCommGroup V4] [Module k V4]
    [AddCommGroup V5] [Module k V5]
    (f : V0 →ₗ[k] V5)
    (e01 : V0 ≃ₗ[k] V1) (e12 : V1 ≃ₗ[k] V2)
    (e23 : V2 ≃ₗ[k] V3) (e34 : V3 ≃ₗ[k] V4)
    (e45 : V4 ≃ₗ[k] V5)
    (hV1 : FiniteDimensional k V1)
    (hf : Function.Injective f) :
    Function.Surjective f := by
  letI : FiniteDimensional k V1 := hV1
  letI : FiniteDimensional k V0 := e01.symm.finiteDimensional
  letI : FiniteDimensional k V2 := e12.finiteDimensional
  letI : FiniteDimensional k V3 := e23.finiteDimensional
  letI : FiniteDimensional k V4 := e34.finiteDimensional
  letI : FiniteDimensional k V5 := e45.finiteDimensional
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (e01.finrank_eq.trans
      (e12.finrank_eq.trans
        (e23.finrank_eq.trans
          (e34.finrank_eq.trans e45.finrank_eq))))).mp
  exact hf

end LinearMap
