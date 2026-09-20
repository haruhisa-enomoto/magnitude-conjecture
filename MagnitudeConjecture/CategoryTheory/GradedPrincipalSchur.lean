import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalDeletion
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd

/-! # Local endomorphisms and distinct shifted principal projectives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable (hdiag : ∀ i, Module.finrank k (cornerComponent R (e i) (e i) 0) = 1)

include he hdiag in
/-- A one-dimensional degree-zero corner gives a local endomorphism ring at
every shift of that principal projective. -/
theorem principalDegree_end_isLocalRing (p : PrincipalDegreeCategory R hmul e he0) :
    IsLocalRing (End p) := by
  have hd : Module.finrank k (End p) = 1 := by
    change Module.finrank k (p ⟶ p) = 1
    rw [(principalDegreeHomEquiv R hmul e he0 he p p).finrank_eq, sub_self]
    exact hdiag p.1
  obtain ⟨E⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one
    (R := k) (S := End p)).2 hd
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm E.toRingEquiv

include he hdiag in
/-- In a nonnegatively graded algebra with diagonal degree-zero corners,
the label and shift of a principal projective are determined by its isomorphism class. -/
theorem principalDegree_skeletal
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (hoff : ∀ i j, i ≠ j → cornerComponent R (e i) (e j) 0 = ⊥) :
    Skeletal (PrincipalDegreeCategory R hmul e he0) := by
  intro p q ⟨E⟩
  letI := principalDegree_end_isLocalRing R hmul e he0 he hdiag p
  letI := principalDegree_end_isLocalRing R hmul e he0 he hdiag q
  have hp : E.hom ≠ 0 := by
    intro hz
    have h : (1 : End p) = 0 := by
      change 𝟙 p = 0
      rw [← E.hom_inv_id, hz, zero_comp]
    exact one_ne_zero h
  have hq : E.inv ≠ 0 := by
    intro hz
    have h : (1 : End q) = 0 := by
      change 𝟙 q = 0
      rw [← E.inv_hom_id, hz, zero_comp]
    exact one_ne_zero h
  have hd : p.2 = q.2 := le_antisymm
    (principalDegree_nonincreasing R hmul e he0 he hneg E.inv hq)
    (principalDegree_nonincreasing R hmul e he0 he hneg E.hom hp)
  have hi : p.1 = q.1 := by
    by_contra hn
    apply hp
    apply (principalDegreeHomEquiv R hmul e he0 he p q).injective
    apply Subtype.ext
    rw [map_zero]
    have h := (principalDegreeHomEquiv R hmul e he0 he p q E.hom).property
    have hz : cornerComponent R (e p.1) (e q.1) (p.2 - q.2) = ⊥ := by
      rw [hd, sub_self, hoff _ _ hn]
    exact hz.le h
  exact Prod.ext hi hd

end MagnitudeConjecture.Graded.FiniteGradedModule
