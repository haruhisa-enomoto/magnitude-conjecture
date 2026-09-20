import MagnitudeConjecture.Algebra.RightModuleDirectUpperSetSquare
import MagnitudeConjecture.Combinatorics.AntichainUpperCube

/-! # Two upper-set squares exclude three-element antichains -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A} {e : A} {D : PrimitiveIdempotentData e}
namespace PrimitiveDirectedBoundaryData

/-- At zero excess every antichain in the projective poset has at most two
elements. Two upper-set squares would otherwise give distinct targets with
the same AR translate. -/
theorem directAntichain_card_le_two
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0)
    (F : Finset B.ProjectivePoset)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a ≤ b → a = b) : F.card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < F.card by omega)
  let U (E : Finset B.ProjectivePoset) := AntichainUpperCube.base F ∪ E
  have hu (E : Finset B.ProjectivePoset) (hE : E ⊆ F) :
      IsUpperSet (U E : Set B.ProjectivePoset) :=
    AntichainUpperCube.union_isUpperSet F E hE
  have hcard (E : Finset B.ProjectivePoset) (hE : E ⊆ F) :
      (U E).card = (AntichainUpperCube.base F).card + E.card :=
    AntichainUpperCube.card_union F E hF hE
  have hinj {E G : Finset B.ProjectivePoset} (hE : E ⊆ F) (hG : G ⊆ F)
      (heq : U E = U G) : E = G :=
    AntichainUpperCube.union_injective F hF hE hG heq
  have hzero : (∅ : Finset B.ProjectivePoset) ⊆ F := Finset.empty_subset F
  have hpair (x y : B.ProjectivePoset) (hx : x ∈ F) (hy : y ∈ F)
      (hxy : x ≠ y) :
      ∃ hn : ¬ (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).IsProjective
          (B.directLineLabel (U {x, y}) (hu _ (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hx, hy]))),
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).tauPlus
          ⟨B.directLineLabel (U {x, y}) (hu _ (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hx, hy])), hn⟩ =
            B.directLineLabel (U ∅) (hu ∅ hzero) := by
    have hsx : ({x} : Finset B.ProjectivePoset) ⊆ F := by simpa using hx
    have hsy : ({y} : Finset B.ProjectivePoset) ⊆ F := by simpa using hy
    have hsxy : ({x, y} : Finset B.ProjectivePoset) ⊆ F := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hx, hy]
    apply B.directUpperSet_square_tauPlus hz (U ∅) (U {x}) (U {y}) (U {x, y})
      (hu _ hzero) (hu _ hsx) (hu _ hsy) (hu _ hsxy)
    · exact Finset.union_subset_union_right (Finset.empty_subset _)
    · exact Finset.union_subset_union_right (by simp)
    · exact Finset.union_subset_union_right (Finset.empty_subset _)
    · exact Finset.union_subset_union_right (by simp)
    · intro heq
      have he := hinj hsx hsy heq
      exact hxy (by simpa using he)
    · simp only [hcard _ hsx, hcard _ hzero, Finset.card_singleton, Finset.card_empty,
        Nat.add_zero]
    · simp only [hcard _ hsy, hcard _ hzero, Finset.card_singleton, Finset.card_empty,
        Nat.add_zero]
    · rw [hcard _ hsxy, hcard _ hsx]
      simp [hxy, Nat.add_assoc]
  have heq := B.directHeight_square_target_unique (hpair a b ha hb hab) (hpair a c ha hc hac)
  have hsets : U {a, b} = U {a, c} := by
    by_contra hne
    exact B.directLineLabel_ne (hu _ (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb]))
      (hu _ (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hc])) hne heq
  have hpairs := hinj (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb]) (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hc]) hsets
  have hm : b ∈ ({a, c} : Finset B.ProjectivePoset) := by rw [← hpairs]; simp
  simpa [hab.symm, hbc] using hm

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
