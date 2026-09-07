import Mathlib.Combinatorics.Quiver.Covering

/-!
# Path lifting with a fixed endpoint

Mathlib's quiver-covering API supplies path-star lifting, with the initial
vertex fixed.  The categorical covering theorem also needs the dual statement
with the terminal vertex fixed.  This file proves it directly from the costar
bijections.
-/

set_option autoImplicit false

open Function Quiver

universe u v

variable {U : Type*} [Quiver.{u} U]
variable {V : Type*} [Quiver.{v} V]
variable (φ : U ⥤q V)

/-- The path costar at `v`: all paths ending at `v`. -/
abbrev Quiver.PathCostar (v : U) := Σ u : U, Path u v

/-- A prefunctor maps the path costar at a vertex into the path costar at
its image. -/
def Prefunctor.pathCostar (v : U) :
    Quiver.PathCostar v → Quiver.PathCostar (φ.obj v) :=
  fun p ↦ ⟨φ.obj p.1, φ.mapPath p.2⟩

@[simp]
theorem Prefunctor.pathCostar_apply {u v : U} (p : Path u v) :
    φ.pathCostar v ⟨u, p⟩ = ⟨φ.obj u, φ.mapPath p⟩ :=
  rfl

theorem Quiver.Path.length_cast_eq {a b a' b' : U}
    (p : Path a b) (ha : a = a') (hb : b = b') :
    (p.cast ha hb).length = p.length := by
  subst a'
  subst b'
  rfl

theorem Prefunctor.pathCostar_surjective
    (hφ : ∀ v, Surjective (φ.costar v)) (v : U) :
    Surjective (φ.pathCostar v) := by
  rintro ⟨u, p⟩
  have aux : ∀ {u c : V} (p : Path u c) (v : U), φ.obj v = c →
      ∃ (u' : U) (q : Path u' v),
        φ.obj u' = u ∧ HEq (φ.mapPath q) p := by
    intro u c p
    induction p with
    | nil =>
        intro v hv
        exact ⟨v, Path.nil, hv, by cases hv; rfl⟩
    | cons p a ih =>
        intro v hv
        cases hv
        obtain ⟨⟨b', a'⟩, ha⟩ := hφ v ⟨_, a⟩
        simp only [Prefunctor.costar_apply, Sigma.mk.inj_iff] at ha
        obtain ⟨hb, ha⟩ := ha
        obtain ⟨u', q, hu, hq⟩ := ih b' hb
        refine ⟨u', q.cons a', hu, ?_⟩
        cases hu
        cases hb
        simp only [heq_eq_eq] at hq ha
        simpa only [Prefunctor.mapPath_cons, hq, ha] using
          (HEq.rfl : p.cons a ≍ p.cons a)
  obtain ⟨u', q, hu, hq⟩ := aux p v rfl
  refine ⟨⟨u', q⟩, ?_⟩
  simp only [Prefunctor.pathCostar_apply, Sigma.mk.inj_iff]
  exact ⟨hu, hq⟩

theorem Prefunctor.pathCostar_injective
    (hφ : ∀ v, Injective (φ.costar v)) (v : U) :
    Injective (φ.pathCostar v) := by
  rintro ⟨u₁, p₁⟩ ⟨u₂, p₂⟩ h
  have aux : ∀ {u₁ v : U} (p₁ : Path u₁ v) {u₂ : U}
      (p₂ : Path u₂ v),
      (⟨φ.obj u₁, φ.mapPath p₁⟩ : Quiver.PathCostar (φ.obj v)) =
        ⟨φ.obj u₂, φ.mapPath p₂⟩ →
      (⟨u₁, p₁⟩ : Quiver.PathCostar v) = ⟨u₂, p₂⟩ := by
    intro u₁ v p₁
    induction p₁ with
    | nil =>
        intro u₂ p₂ h
        rcases p₂ with - | ⟨p₂, e₂⟩
        · rfl
        · simp only [Prefunctor.mapPath_cons, Sigma.mk.inj_iff] at h
          obtain ⟨hu, hp⟩ := h
          rw [← Path.cast_eq_iff_heq hu rfl] at hp
          have hlength := congrArg Path.length hp
          rw [Path.length_cast_eq] at hlength
          simp at hlength
    | cons p₁ e₁ ih =>
        intro u₂ p₂ h
        rcases p₂ with - | ⟨p₂, e₂⟩
        · simp only [Prefunctor.mapPath_cons, Sigma.mk.inj_iff] at h
          obtain ⟨hu, hp⟩ := h
          rw [← Path.eq_cast_iff_heq hu.symm rfl] at hp
          have hlength := congrArg Path.length hp
          rw [Path.length_cast_eq] at hlength
          simp at hlength
        · rename_i b₂
          simp only [Prefunctor.mapPath_cons, Sigma.mk.inj_iff] at h
          obtain ⟨hu, hp⟩ := h
          rw [← Path.cast_eq_iff_heq hu rfl, Path.cast_cons] at hp
          have hb := Path.obj_eq_of_cons_eq_cons hp
          have hpath := Path.heq_of_cons_eq_cons hp
          have he : HEq (φ.map e₁) (φ.map e₂) :=
            (Hom.cast_heq _ _ (φ.map e₁)).symm.trans
              (Path.hom_heq_of_cons_eq_cons hp)
          have hcostar : φ.costar _ ⟨_, e₁⟩ = φ.costar _ ⟨b₂, e₂⟩ := by
            simp only [Prefunctor.costar_apply, Sigma.mk.inj_iff]
            exact ⟨hb, he⟩
          cases hφ _ hcostar
          have hpath' : HEq (φ.mapPath p₁) (φ.mapPath p₂) :=
            (Path.cast_heq _ _ (φ.mapPath p₁)).symm.trans hpath
          have hrec :
              (⟨φ.obj u₁, φ.mapPath p₁⟩ :
                Quiver.PathCostar (φ.obj _)) =
                ⟨φ.obj u₂, φ.mapPath p₂⟩ := by
            exact Sigma.ext hu hpath'
          cases ih p₂ hrec
          rfl
  exact aux p₁ p₂ h

theorem Prefunctor.pathCostar_bijective
    (hφ : ∀ v, Bijective (φ.costar v)) (v : U) :
    Bijective (φ.pathCostar v) :=
  ⟨φ.pathCostar_injective (fun v ↦ (hφ v).1) v,
    φ.pathCostar_surjective (fun v ↦ (hφ v).2) v⟩

namespace Prefunctor.IsCovering

variable {φ}

/-- A quiver covering gives unique path lifting with the terminal vertex
fixed. -/
protected theorem pathCostar_bijective (hφ : φ.IsCovering) (v : U) :
    Bijective (φ.pathCostar v) :=
  φ.pathCostar_bijective hφ.costar_bijective v

end Prefunctor.IsCovering
