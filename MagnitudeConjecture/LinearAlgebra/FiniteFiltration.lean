import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# Finite filtrations and reflection of linear isomorphisms

A linear map which is bijective on a filtration term and on the next
successive quotient is bijective on the next term.  Iterating this elementary
fact is the linear-algebra endpoint of the finite elementary-interval
filtration used by string detectors.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.LinearAlgebra.FiniteFiltration

universe u

variable {k V W : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- Restrict a linear map to specified source and target subspaces. -/
def restrictionMap (f : V →ₗ[k] W) (U : Submodule k V) (U' : Submodule k W)
    (h : U.map f ≤ U') : U →ₗ[k] U' :=
  LinearMap.codRestrict U' (f.domRestrict U) (by
    intro x
    exact h ⟨x, x.2, rfl⟩)

@[simp]
theorem restrictionMap_coe (f : V →ₗ[k] W)
    (U : Submodule k V) (U' : Submodule k W)
    (h : U.map f ≤ U') (x : U) :
    (restrictionMap f U U' h x : W) = f x :=
  rfl

/-- The map induced on one successive quotient of two compatible filtered
spaces. -/
def layerMap (f : V →ₗ[k] W)
    (U X : Submodule k V) (U' X' : Submodule k W)
    (_hUX : U ≤ X) (_hU'X' : U' ≤ X')
    (hX : X.map f ≤ X') (hU : U.map f ≤ U') :
    (X ⧸ U.comap X.subtype) →ₗ[k]
      (X' ⧸ U'.comap X'.subtype) :=
  Submodule.mapQ (U.comap X.subtype) (U'.comap X'.subtype)
    (restrictionMap f X X' hX) (by
      rintro x hx
      change f x.1 ∈ U'
      exact hU ⟨x.1, hx, rfl⟩)

@[simp]
theorem layerMap_mk (f : V →ₗ[k] W)
    (U X : Submodule k V) (U' X' : Submodule k W)
    (hUX : U ≤ X) (hU'X' : U' ≤ X')
    (hX : X.map f ≤ X') (hU : U.map f ≤ U') (x : X) :
    layerMap f U X U' X' hUX hU'X' hX hU
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (restrictionMap f X X' hX x) :=
  Submodule.mapQ_apply _ _ _ x

/-- Bijectivity on one filtration term and the following quotient implies
bijectivity on the following term. -/
theorem restrictionMap_bijective_of_layerMap_bijective
    (f : V →ₗ[k] W)
    (U X : Submodule k V) (U' X' : Submodule k W)
    (hUX : U ≤ X) (hU'X' : U' ≤ X')
    (hX : X.map f ≤ X') (hU : U.map f ≤ U')
    (hbase : Function.Bijective (restrictionMap f U U' hU))
    (hlayer : Function.Bijective
      (layerMap f U X U' X' hUX hU'X' hX hU)) :
    Function.Bijective (restrictionMap f X X' hX) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hfx : f x.1 = 0 := by
      exact congrArg Subtype.val hx
    have hquotZero :
        layerMap f U X U' X' hUX hU'X' hX hU
            (Submodule.Quotient.mk x) = 0 := by
      rw [layerMap_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change f x.1 ∈ U'
      rw [hfx]
      exact U'.zero_mem
    have hxQuot : (Submodule.Quotient.mk x :
        X ⧸ U.comap X.subtype) = 0 := by
      exact hlayer.1 (by simpa using hquotZero)
    have hxU : x.1 ∈ U := by
      exact (Submodule.Quotient.mk_eq_zero
        (U.comap X.subtype)).mp hxQuot
    let xU : U := ⟨x.1, hxU⟩
    have hxUZero : restrictionMap f U U' hU xU = 0 := by
      apply Subtype.ext
      exact hfx
    have : xU = 0 := by
      apply hbase.1
      simpa using hxUZero
    apply Subtype.ext
    change x.1 = 0
    simpa only [xU, Submodule.coe_zero] using congrArg Subtype.val this
  · intro y
    obtain ⟨q, hq⟩ := hlayer.2 (Submodule.Quotient.mk y)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
      (U.comap X.subtype) q
    rw [layerMap_mk] at hq
    have hdiff :
        (restrictionMap f X X' hX x : W) - y.1 ∈ U' := by
      exact (Submodule.Quotient.eq (U'.comap X'.subtype)).mp hq
    let correction : U' :=
      ⟨y.1 - f x.1, by
        have hneg := U'.neg_mem hdiff
        simpa [restrictionMap_coe] using hneg⟩
    obtain ⟨u, hu⟩ := hbase.2 correction
    let z : X := ⟨x.1 + u.1, X.add_mem x.2 (hUX u.2)⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    have hu' := congrArg Subtype.val hu
    change f (x.1 + u.1) = y.1
    rw [map_add]
    change f x.1 + (restrictionMap f U U' hU u : W) = y.1
    rw [hu']
    dsimp only [correction]
    abel

/-- A finite increasing filtration from zero to the whole vector space.  The
natural number `n` is the number of successive layers. -/
structure Filtration (k V : Type u) [Field k]
    [AddCommGroup V] [Module k V] (n : ℕ) where
  subspace : Fin (n + 1) → Submodule k V
  monotone_subspace : Monotone subspace
  subspace_zero : subspace 0 = ⊥
  subspace_last : subspace (Fin.last n) = ⊤

namespace Filtration

variable {n : ℕ}

/-- A linear map preserves two filtrations with the same finite index. -/
def Compatible (f : V →ₗ[k] W)
    (F : Filtration k V n) (G : Filtration k W n) : Prop :=
  ∀ i, (F.subspace i).map f ≤ G.subspace i

/-- The map induced on the `i`th successive filtration quotient. -/
def gradedMap (f : V →ₗ[k] W)
    (F : Filtration k V n) (G : Filtration k W n)
    (h : Compatible f F G) (i : Fin n) :
    (F.subspace i.succ ⧸
        (F.subspace i.castSucc).comap (F.subspace i.succ).subtype) →ₗ[k]
      (G.subspace i.succ ⧸
        (G.subspace i.castSucc).comap (G.subspace i.succ).subtype) :=
  layerMap f (F.subspace i.castSucc) (F.subspace i.succ)
    (G.subspace i.castSucc) (G.subspace i.succ)
    (F.monotone_subspace i.castSucc_le_succ)
    (G.monotone_subspace i.castSucc_le_succ) (h i.succ) (h i.castSucc)

/-- Bijectivity on every successive quotient of two compatible finite
filtrations implies bijectivity of the original linear map. -/
theorem map_bijective_of_gradedMap_bijective
    (f : V →ₗ[k] W)
    (F : Filtration k V n) (G : Filtration k W n)
    (h : Compatible f F G)
    (hgraded : ∀ i, Function.Bijective (gradedMap f F G h i)) :
    Function.Bijective f := by
  have hterm : ∀ i : Fin (n + 1), Function.Bijective
      (restrictionMap f (F.subspace i) (G.subspace i) (h i)) := by
    intro i
    induction i using Fin.induction with
    | zero =>
        constructor
        · intro x y _
          apply Subtype.ext
          have hx : x.1 = 0 := by
            have hxmem : x.1 ∈ (⊥ : Submodule k V) :=
              F.subspace_zero ▸ x.2
            exact hxmem
          have hy : y.1 = 0 := by
            have hymem : y.1 ∈ (⊥ : Submodule k V) :=
              F.subspace_zero ▸ y.2
            exact hymem
          exact hx.trans hy.symm
        · intro y
          refine ⟨0, ?_⟩
          apply Subtype.ext
          have hy : y.1 = 0 := by
            have hymem : y.1 ∈ (⊥ : Submodule k W) :=
              G.subspace_zero ▸ y.2
            exact hymem
          simpa only [restrictionMap_coe, map_zero,
            Submodule.coe_zero] using hy.symm
    | succ i ih =>
        exact restrictionMap_bijective_of_layerMap_bijective f
          (F.subspace i.castSucc) (F.subspace i.succ)
          (G.subspace i.castSucc) (G.subspace i.succ)
          (F.monotone_subspace i.castSucc_le_succ)
          (G.monotone_subspace i.castSucc_le_succ)
          (h i.succ) (h i.castSucc) ih (hgraded i)
  have hlast := hterm (Fin.last n)
  constructor
  · intro x y hxy
    let xTop : (⊤ : Submodule k V) := ⟨x, trivial⟩
    let yTop : (⊤ : Submodule k V) := ⟨y, trivial⟩
    have hrestricted :
        restrictionMap f (F.subspace (Fin.last n))
            (G.subspace (Fin.last n)) (h (Fin.last n))
            ⟨x, by rw [F.subspace_last]; trivial⟩ =
          restrictionMap f (F.subspace (Fin.last n))
            (G.subspace (Fin.last n)) (h (Fin.last n))
            ⟨y, by rw [F.subspace_last]; trivial⟩ := by
      apply Subtype.ext
      exact hxy
    have hxyTop := hlast.1 hrestricted
    exact congrArg Subtype.val hxyTop
  · intro y
    let yLast : G.subspace (Fin.last n) :=
      ⟨y, by rw [G.subspace_last]; trivial⟩
    obtain ⟨xLast, hxLast⟩ := hlast.2 yLast
    refine ⟨xLast.1, ?_⟩
    exact congrArg Subtype.val hxLast

end Filtration

end MagnitudeConjecture.LinearAlgebra.FiniteFiltration
