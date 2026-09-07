import MagnitudeConjecture.Algebra.RightModuleFiniteType
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Two-sided ideals of a representation-finite algebra

Every finite-dimensional right module over a representation-finite algebra
is a finite direct sum of members of one fixed finite indecomposable family.
Annihilators turn direct sums into intersections, and every two-sided ideal
is the annihilator of the corresponding regular quotient.  Consequently the
two-sided ideal lattice is finite.

The proof is the right-module migration of the Jans finite-ideal argument
formalized in `CartanDeterminant.Algebra.RepresentationFiniteIdeals` at
homological-conjectures commit `60736a0a`.  It is reproduced here so the
magnitude package remains Mathlib-only.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- A finite-dimensional representation-finite algebra has only finitely
many two-sided ideals.  The decomposition argument is first run on the
literal left-module model over `Aᵐᵒᵖ`; the final statement is transported
back along the order isomorphism between ideals of a ring and its opposite.
-/
theorem IsRepresentationFinite.finite_twoSidedIdeal
    [FiniteDimensional k A]
    (hA : IsRepresentationFinite k A) :
    Finite (TwoSidedIdeal A) := by
  have hopFinite : Finite (TwoSidedIdeal Aᵐᵒᵖ) := by
    obtain ⟨n, X, _hX, hcover⟩ := hA
    let ann : ModuleCat.{u} Aᵐᵒᵖ → TwoSidedIdeal Aᵐᵒᵖ := fun M ↦
      (Module.annihilator Aᵐᵒᵖ M).toTwoSided
    have ann_iso {M N : ModuleCat.{u} Aᵐᵒᵖ} (e : M ≅ N) :
        ann M = ann N := by
      apply TwoSidedIdeal.ext
      intro a
      simp only [ann, Ideal.mem_toTwoSided]
      rw [e.toLinearEquiv.annihilator_eq]
    have ann_prod (M N : ModuleCat.{u} Aᵐᵒᵖ) :
        ann (ModuleCat.of Aᵐᵒᵖ (M × N)) = ann M ⊓ ann N := by
      apply TwoSidedIdeal.ext
      intro a
      simp only [ann, Ideal.mem_toTwoSided, TwoSidedIdeal.mem_inf]
      rw [Module.annihilator_prod]
      rfl
    let Q : ℕ → Prop := fun d ↦
      ∀ (M : ModuleCat.{u} Aᵐᵒᵖ) [Module.Finite k M],
        Module.finrank k M = d →
        ∃ s : Finset (Fin n), ann M = s.inf (fun i ↦ ann (X i))
    have hQ : ∀ d, Q d := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
          intro M hMfin hMdim
          by_cases hMzero : IsZero M
          · refine ⟨∅, ?_⟩
            rw [Finset.inf_empty]
            apply TwoSidedIdeal.ext
            intro a
            simp only [ann, Ideal.mem_toTwoSided]
            constructor
            · exact fun _ ↦ TwoSidedIdeal.mem_top Aᵐᵒᵖ
            · intro _
              rw [Module.mem_annihilator]
              intro m
              exact (ModuleCat.isZero_iff_subsingleton.mp hMzero).elim _ _
          by_cases hMind : Indecomposable M
          · obtain ⟨i, ⟨e⟩⟩ := hcover M ⟨inferInstance, hMind⟩
            refine ⟨{i}, ?_⟩
            rw [Finset.inf_singleton]
            exact ann_iso e
          · rw [Indecomposable] at hMind
            push Not at hMind
            rcases hMind hMzero with ⟨Y, Z, e, hY, hZ⟩
            let pY : Y ⟶ M := biprod.inl ≫ e.inv
            let rY : M ⟶ Y := e.hom ≫ biprod.fst
            have hpYrY : pY ≫ rY = 𝟙 Y := by
              simp [pY, rY, Category.assoc]
            have hleftY : Function.LeftInverse rY pY := by
              intro y
              change (pY ≫ rY) y = y
              rw [hpYrY]
              rfl
            letI : Module.Finite k Y :=
              Module.Finite.of_injective (pY.hom.restrictScalars k)
                hleftY.injective
            let pZ : Z ⟶ M := biprod.inr ≫ e.inv
            let rZ : M ⟶ Z := e.hom ≫ biprod.snd
            have hpZrZ : pZ ≫ rZ = 𝟙 Z := by
              simp [pZ, rZ, Category.assoc]
            have hleftZ : Function.LeftInverse rZ pZ := by
              intro z
              change (pZ ≫ rZ) z = z
              rw [hpZrZ]
              rfl
            letI : Module.Finite k Z :=
              Module.Finite.of_injective (pZ.hom.restrictScalars k)
                hleftZ.injective
            have hYnsub : ¬ Subsingleton Y :=
              (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hY
            have hZnsub : ¬ Subsingleton Z :=
              (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hZ
            letI : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hYnsub
            letI : Nontrivial Z := not_subsingleton_iff_nontrivial.mp hZnsub
            have hdim : Module.finrank k M =
                Module.finrank k Y + Module.finrank k Z := by
              calc
                Module.finrank k M =
                    Module.finrank k (Y ⊞ Z : ModuleCat.{u} (Aᵐᵒᵖ)) :=
                  LinearEquiv.finrank_eq
                    (e.toLinearEquiv.restrictScalars k)
                _ = Module.finrank k (ModuleCat.of Aᵐᵒᵖ (Y × Z)) :=
                  LinearEquiv.finrank_eq
                    ((ModuleCat.biprodIsoProd Y Z).toLinearEquiv.restrictScalars k)
                _ = Module.finrank k Y + Module.finrank k Z :=
                  Module.finrank_prod
            have hYlt : Module.finrank k Y < d := by
              rw [← hMdim, hdim]
              exact Nat.lt_add_of_pos_right Module.finrank_pos
            have hZlt : Module.finrank k Z < d := by
              rw [← hMdim, hdim]
              exact Nat.lt_add_of_pos_left Module.finrank_pos
            obtain ⟨sY, hsY⟩ := ih (Module.finrank k Y) hYlt Y rfl
            obtain ⟨sZ, hsZ⟩ := ih (Module.finrank k Z) hZlt Z rfl
            refine ⟨sY ∪ sZ, ?_⟩
            rw [Finset.inf_union, ← hsY, ← hsZ]
            exact (ann_iso e).trans <|
              (ann_iso (ModuleCat.biprodIsoProd Y Z)).trans (ann_prod Y Z)
    let decode : Finset (Fin n) → TwoSidedIdeal Aᵐᵒᵖ := fun s ↦
      s.inf (fun i ↦ ann (X i))
    apply Finite.of_surjective decode
    intro I
    let M : ModuleCat.{u} Aᵐᵒᵖ := ModuleCat.of Aᵐᵒᵖ (Aᵐᵒᵖ ⧸ I.asIdeal)
    let targetMod : Module k M :=
      ModuleCat.Algebra.instModuleCarrier (S₀ := k) (S := Aᵐᵒᵖ) (M := M)
    let qA : Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] M := I.asIdeal.mkQ
    let qk : @LinearMap k k _ _ (RingHom.id k) Aᵐᵒᵖ M _ _
        Algebra.toModule targetMod :=
      { toFun := qA
        map_add' := qA.map_add
        map_smul' := by
          intro c x
          rw [Algebra.smul_def]
          exact qA.map_smul (algebraMap k Aᵐᵒᵖ c) x }
    have hMfin : @Module.Finite k M _ _ targetMod :=
      Module.Finite.of_surjective qk I.asIdeal.mkQ_surjective
    have hMfin' : @Module.Finite k M _ _
        (ModuleCat.Algebra.instModuleCarrier (S₀ := k) (S := Aᵐᵒᵖ) (M := M)) := by
      simpa [targetMod] using hMfin
    obtain ⟨s, hs⟩ := @hQ (Module.finrank k M) M hMfin' rfl
    refine ⟨s, ?_⟩
    change s.inf (fun i ↦ ann (X i)) = I
    rw [← hs]
    apply TwoSidedIdeal.ext
    intro a
    simp only [ann, Ideal.mem_toTwoSided]
    change a ∈ Module.annihilator Aᵐᵒᵖ (Aᵐᵒᵖ ⧸ I.asIdeal) ↔ a ∈ I
    rw [Ideal.annihilator_quotient]
    rfl
  exact Finite.of_injective
    (fun I : TwoSidedIdeal A ↦ I.op)
    (TwoSidedIdeal.opOrderIso (R := A)).injective

end MagnitudeConjecture.RightModule
