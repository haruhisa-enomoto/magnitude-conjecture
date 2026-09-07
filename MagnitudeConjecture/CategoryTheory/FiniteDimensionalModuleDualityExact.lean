import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDuality
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Exactness consequences of finite coefficient duality

The pointwise coefficient-duality anti-equivalence reverses monomorphisms
and epimorphisms.  These two small interfaces are the categorical input for
the Auslander--Reiten socle-length calculation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- Coefficient duality sends an epimorphism of finite modules to a
monomorphism. -/
theorem finiteCoefficientDual_map_mono_of_epi
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : M ⟶ N) [Epi f] :
    Mono ((finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map f.op) := by
  exact (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map_mono f.op

/-- Coefficient duality sends a monomorphism of finite modules to an
epimorphism. -/
theorem finiteCoefficientDual_map_epi_of_mono
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : M ⟶ N) [Mono f] :
    Epi ((finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map f.op) := by
  exact (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map_epi f.op

/-- A finite-module map is epic exactly when its coefficient dual is monic. -/
theorem finiteCoefficientDual_map_mono_iff_epi
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : M ⟶ N) :
    Mono ((finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map f.op) ↔
      Epi f := by
  constructor
  · intro h
    letI : Mono ((finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map f.op) := h
    letI : Mono f.op :=
      (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.mono_of_mono_map
        inferInstance
    exact unop_epi_of_mono f.op
  · intro h
    letI : Epi f := h
    exact finiteCoefficientDual_map_mono_of_epi f

/-- A finite-module map is monic exactly when its coefficient dual is epic. -/
theorem finiteCoefficientDual_map_epi_iff_mono
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : M ⟶ N) :
    Epi ((finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map f.op) ↔
      Mono f := by
  constructor
  · intro h
    letI : Epi ((finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.map f.op) := h
    letI : Epi f.op :=
      (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.epi_of_epi_map
        inferInstance
    exact unop_mono_of_epi f.op
  · intro h
    letI : Mono f := h
    exact finiteCoefficientDual_map_epi_of_mono f

/-- Coefficient duality carries a short exact sequence to its reversed short
exact sequence. -/
theorem finiteCoefficientDual_map_shortExact
    (S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    (hS : S.ShortExact) :
    (S.op.map
      (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor).ShortExact := by
  exact hS.op.map_of_exact
    (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor

/-- A short complex is short exact exactly when its coefficient-dual reversal
is short exact. -/
theorem finiteCoefficientDual_map_shortExact_iff
    (S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)) :
    (S.op.map
      (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor).ShortExact ↔
      S.ShortExact := by
  exact
    (CategoryTheory.ShortExact.shortExact_map_iff
      (finiteCoefficientDualityEquivalence (k := k) (C := C)).functor).trans
      S.shortExact_iff_op.symm

end MagnitudeConjecture.CoveringHom
