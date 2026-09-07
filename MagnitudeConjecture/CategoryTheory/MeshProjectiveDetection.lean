import MagnitudeConjecture.CategoryTheory.MeshRiedtmann
import MagnitudeConjecture.CategoryTheory.RestrictedYoneda

/-!
# Projective detection in a finite Riedtmann mesh

Riedtmann condition (b) lets a nonzero morphism be pulled backwards through
an incoming arrow as long as its source vertex is nonprojective.  Finite-
dimensionality of the graded mesh Hom spaces makes their path-length
filtration terminate.  Consequently this backwards process reaches a
projective vertex, which is precisely the faithfulness input for restricted
Yoneda on the projective full subcategory.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory

universe u

variable {k : Type u} [Field k]
variable {Q : Type} [Quiver Q]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- For a fixed target vertex, finite-dimensionality gives a common cutoff
at which every source-to-target path-length tail vanishes. -/
theorem exists_uniform_source_lengthTail_eq_bot
    (hfinite : ∀ x y : Q,
      FiniteDimensional k (obj (k := k) T x ⟶ obj (k := k) T y))
    (x : Q) :
    ∃ N, ∀ z : Q, lengthTail (k := k) T z x N = ⊥ := by
  classical
  let cutoff (z : Q) :=
    Classical.choose (exists_lengthComponent_cutoff (k := k) T z x)
  have hcutoff (z : Q) : ∀ d, cutoff z ≤ d →
      lengthComponent (k := k) T z x d = ⊥ :=
    Classical.choose_spec (exists_lengthComponent_cutoff (k := k) T z x)
  let N := ∑ z : Q, cutoff z
  refine ⟨N, fun z ↦ ?_⟩
  apply lengthTail_eq_bot_of_components (k := k) T z x N
  intro d hd
  apply hcutoff z d
  exact (Finset.single_le_sum
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ z)).trans hd

/-- If no projective vertex detects a nonzero morphism, condition (b) can
construct arbitrarily long nonvanishing precompositions. -/
theorem exists_lengthTail_precomposition_ne_zero
    (hB : T.RiedtmannConditionB (k := k))
    {x y : Q} (f : obj (k := k) T x ⟶ obj (k := k) T y)
    (hf : f ≠ 0)
    (hprojective : ∀ (p : Q), p ∈ T.projective →
      ∀ g : obj (k := k) T p ⟶ obj (k := k) T x, g ≫ f = 0) :
    ∀ n, ∃ (z : Q) (g : obj (k := k) T z ⟶ obj (k := k) T x),
      g ∈ lengthTail (k := k) T z x n ∧ g ≫ f ≠ 0 := by
  intro n
  induction n with
  | zero =>
      refine ⟨x, 𝟙 _, ?_, ?_⟩
      · rw [lengthTail_zero_eq_top]
        exact Submodule.mem_top
      · simpa using hf
  | succ n ih =>
      obtain ⟨z, g, hgTail, hgf⟩ := ih
      have hz : z ∉ T.projective := by
        intro hz
        exact hgf (hprojective z hz g)
      obtain ⟨a, ha⟩ := hB ⟨z, hz⟩ y (g ≫ f) hgf
      let q := T.incomingArrowHom (k := k) a ≫ g
      refine ⟨a.1, q, ?_, ?_⟩
      · have haTail : T.incomingArrowHom (k := k) a ∈
            lengthTail (k := k) T a.1 z 1 :=
          mem_lengthTail_of_mem_lengthComponent (k := k) T (by omega)
            (T.incomingArrowHom_mem_lengthComponent_one (k := k) a)
        simpa [q, Nat.add_comm] using
          comp_mem_lengthTail (k := k) T haTail hgTail
      · simpa [q, Category.assoc] using ha

/-- Riedtmann condition (b) and Hom-finiteness make the projective vertices
a detecting family for all morphisms in the raw mesh category. -/
theorem exists_projective_precomposition_ne_zero
    (hfinite : ∀ x y : Q,
      FiniteDimensional k (obj (k := k) T x ⟶ obj (k := k) T y))
    (hB : T.RiedtmannConditionB (k := k))
    {x y : Q} (f : obj (k := k) T x ⟶ obj (k := k) T y)
    (hf : f ≠ 0) :
    ∃ (p : Q) (_ : p ∈ T.projective)
      (g : obj (k := k) T p ⟶ obj (k := k) T x), g ≫ f ≠ 0 := by
  by_contra hnone
  push Not at hnone
  obtain ⟨N, hN⟩ := T.exists_uniform_source_lengthTail_eq_bot hfinite x
  obtain ⟨z, g, hgTail, hgf⟩ :=
    T.exists_lengthTail_precomposition_ne_zero hB f hf
      (fun p hp q ↦ hnone p hp q) N
  have hg : g = 0 := by
    rw [hN z] at hgTail
    simpa using hgTail
  exact hgf (by simp [hg])

end RightMeshData

end MagnitudeConjecture.MeshCategory
