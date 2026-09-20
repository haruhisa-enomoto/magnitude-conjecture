import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalAlgebra
import MagnitudeConjecture.CategoryTheory.GradedPrincipalSchur
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraSimpleCount

/-! # The exact simple-module count of a finite graded interval -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable (hdiag : ∀ i, Module.finrank k (cornerComponent R (e i) (e i) 0) = 1)

local instance intervalSimpleCountFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m) :=
  inferInstanceAs (Fintype (ι × Fin (m + 1)))
local instance intervalSimpleCountOpFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite
local instance intervalSimpleCountFinite (m : ℕ) :
    FiniteDimensional k (principalIntervalAlgebra R hmul e he0 he m) :=
  principalIntervalAlgebra_finiteDimensional R hmul e he0 he m
local instance intervalSimpleCountNoetherian (m : ℕ) :
    IsNoetherianRing (principalIntervalAlgebra R hmul e he0 he m)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

include he hdiag in
/-- The interval's opposite category has local endomorphism rings. -/
theorem principalIntervalOp_end_isLocalRing (m : ℕ)
    (p : (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ) :
    IsLocalRing (End p) := by
  let E : (p ⟶ p) ≃ₗ[k]
      cornerComponent R (e p.unop.1) (e p.unop.1)
        ((p.unop.2.val : ℤ) - p.unop.2.val) :=
    (CoveringHom.oppositeHomLinearEquiv (k := k) p p).trans
      (InducedCategory.homLinearEquiv.trans
        (principalDegreeHomEquiv R hmul e he0 he _ _))
  have hd : Module.finrank k (End p) = 1 := by
    change Module.finrank k (p ⟶ p) = 1
    rw [E.finrank_eq, sub_self]
    exact hdiag p.unop.1
  obtain ⟨F⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one
    (R := k) (S := End p)).2 hd
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm F.toRingEquiv

include he hdiag in
/-- Restricting the skeletal degree category to a finite interval and taking
the opposite preserves distinct labels. -/
theorem principalIntervalOp_skeletal
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (hoff : ∀ i j, i ≠ j → cornerComponent R (e i) (e j) 0 = ⊥)
    (m : ℕ) : Skeletal (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ := by
  intro p q ⟨E⟩
  have h := principalDegree_skeletal R hmul e he0 he hdiag hneg hoff
    ⟨(principalIntervalInclusion R hmul e he0 m).mapIso E.unop.symm⟩
  apply Opposite.unop_injective
  apply Prod.ext
  · exact congrArg (fun x : PrincipalDegreeCategory R hmul e he0 ↦ x.1) h
  · apply Fin.ext
    have hd := congrArg Prod.snd h
    change (p.unop.2.val : ℤ) = q.unop.2.val at hd
    exact_mod_cast hd

include hdiag in
/-- Each primitive label contributes exactly one simple class in each degree
of the interval, independently of the widths of the indecomposable modules. -/
theorem principalIntervalAlgebra_simpleCount
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (hoff : ∀ i j, i ≠ j → cornerComponent R (e i) (e j) 0 = ⊥)
    (m : ℕ)
    (S : RightModule.FiniteIndecomposableSkeleton k
      (principalIntervalAlgebra R hmul e he0 he m)) :
    S.simpleCount = Fintype.card ι * (m + 1) := by
  have h := CoveringHom.finiteCategoryAlgebra_simpleCount_of_algEquiv
    (principalIntervalFiniteRepresentables R hmul e he0 he m)
    (principalIntervalAlgebraRepresentableEquiv R hmul e he0 he m)
    (principalIntervalOp_end_isLocalRing R hmul e he0 he hdiag m)
    (principalIntervalOp_skeletal R hmul e he0 he hdiag hneg hoff m) S
  rw [h, ← Fintype.card_congr (Opposite.equivToOpposite
    (α := PrincipalIntervalCategory R hmul e he0 m))]
  change Fintype.card (ι × Fin (m + 1)) = _
  rw [Fintype.card_prod, Fintype.card_fin]

end MagnitudeConjecture.Graded.FiniteGradedModule
