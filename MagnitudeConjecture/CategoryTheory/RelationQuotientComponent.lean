import MagnitudeConjecture.CategoryTheory.HomogeneousRelationQuotient

/-! # Components unaffected by the relation ideal -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.LinearPathCategory
open QuotientSubmoduleEquidistribution.CategoricalIdeal
universe u v w
variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q]

/-- A homogeneous morphism has no coefficient at a path of another length. -/
theorem pathCoefficient_eq_zero {X Y : Category k Q} {n : ℕ} {f : X ⟶ Y}
    (hf : f ∈ lengthComponent X Y n)
    (p : Quiver.Path (vertex Y) (vertex X)) (hp : p.length ≠ n) :
    homPathLinearEquiv X Y f p = 0 := by
  rw [← Finsupp.notMem_support_iff]
  intro h
  exact hp ((mem_lengthComponent_iff X Y n f).mp hf h)

namespace HomogeneousQuotient

/-- If every path-basis composite of a relation avoids degree n, the quotient
map is injective on that degree. -/
theorem component_quotient_injective
    (R : ∀ X Y : Category k Q, Set (X ⟶ Y)) (X Y : Category k Q) (n : ℕ)
    (hR : ∀ f, f ∈ basisCompositeSet R X Y →
      ∃ m, m ≠ n ∧ f ∈ LinearPathCategory.lengthComponent X Y m) :
    Function.Injective ((quotientHomLinearMap R X Y).submoduleMap
      (LinearPathCategory.lengthComponent X Y n)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro f hf
  have hk : (f : X ⟶ Y) ∈ HomIdeal.generatedHomSubmodule k R X Y := by
    rw [← ker_quotientHomLinearMap, LinearMap.mem_ker]
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hf)
  have hz : (f : X ⟶ Y) = 0 := by
    apply (homPathLinearEquiv X Y).injective
    ext p
    change homPathLinearEquiv X Y f.val p = homPathLinearEquiv X Y 0 p
    rw [map_zero, Finsupp.zero_apply]
    by_cases hp : p.length = n
    · let ev : (X ⟶ Y) →ₗ[k] k :=
        (Finsupp.lapply p).comp (homPathLinearEquiv X Y).toLinearMap
      have hle : HomIdeal.generatedHomSubmodule k R X Y ≤ LinearMap.ker ev := by
        rw [generatedHomSubmodule_eq_span_basisCompositeSet]
        apply Submodule.span_le.mpr
        intro g hg
        obtain ⟨m, hmn, hgm⟩ := hR g hg
        change homPathLinearEquiv X Y g p = 0
        exact pathCoefficient_eq_zero hgm p (by simpa [hp] using Ne.symm hmn)
      exact hle hk
    · exact pathCoefficient_eq_zero f.property p hp
  change f = 0
  exact Subtype.ext hz

/-- A degree avoided by all relation composites survives unchanged. -/
def componentEquiv
    (R : ∀ X Y : Category k Q, Set (X ⟶ Y)) (X Y : Category k Q) (n : ℕ)
    (hR : ∀ f, f ∈ basisCompositeSet R X Y →
      ∃ m, m ≠ n ∧ f ∈ LinearPathCategory.lengthComponent X Y m) :
    LinearPathCategory.lengthComponent X Y n ≃ₗ[k] lengthComponent R X Y n :=
  LinearEquiv.ofBijective ((quotientHomLinearMap R X Y).submoduleMap _)
    ⟨component_quotient_injective R X Y n hR,
      (quotientHomLinearMap R X Y).submoduleMap_surjective _⟩

end HomogeneousQuotient
end MagnitudeConjecture.LinearPathCategory
