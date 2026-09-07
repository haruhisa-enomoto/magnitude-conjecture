import MagnitudeConjecture.CategoryTheory.PathLengthGrading
import MagnitudeConjecture.CategoryTheory.LinearPathLift

/-!
# Kernels and the path-length filtration

A linear realization of a free path category has no kernel terms below a
cutoff when the short realized paths remain linearly independent modulo a
target submodule containing every long realized path.  The cutoff-two case is
the generic linear-algebra step in ordinary-quiver admissibility.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.LinearPathCategory

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type z} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]

theorem exists_eq_toPath_of_length_one {x y : Q} (p : Quiver.Path x y)
    (hp : p.length = 1) :
    ∃ a : x ⟶ y, p = a.toPath := by
  obtain ⟨c, a, q, hq, hpath⟩ :=
    Quiver.Path.eq_toPath_comp_of_length_eq_succ p hp
  have hcy : c = y := q.eq_of_length_zero hq
  subst c
  rw [q.eq_nil_of_length_zero hq, Quiver.Path.comp_nil] at hpath
  exact ⟨a, hpath⟩

/-- Recover the unique arrow represented by a path of length one. -/
def arrowOfLengthOne {x y : Q}
    (p : {p : Quiver.Path x y // p.length = 1}) : x ⟶ y :=
  Classical.choose (exists_eq_toPath_of_length_one p.1 p.2)

theorem lengthOnePath_eq_toPath {x y : Q}
    (p : {p : Quiver.Path x y // p.length = 1}) :
    p.1 = (arrowOfLengthOne p).toPath :=
  Classical.choose_spec (exists_eq_toPath_of_length_one p.1 p.2)

@[simp]
theorem arrowOfLengthOne_toPath {x y : Q} (a : x ⟶ y) :
    arrowOfLengthOne ⟨a.toPath, rfl⟩ = a := by
  have h := lengthOnePath_eq_toPath
    (⟨a.toPath, rfl⟩ : {p : Quiver.Path x y // p.length = 1})
  injection h.symm

theorem arrowOfLengthOne_injective {x y : Q} :
    Function.Injective (arrowOfLengthOne (Q := Q) :
      {p : Quiver.Path x y // p.length = 1} → (x ⟶ y)) := by
  intro p q h
  apply Subtype.ext
  rw [lengthOnePath_eq_toPath p, lengthOnePath_eq_toPath q, h]

/-- Arrows are equivalent to paths of length one. -/
def arrowEquivLengthOnePath (x y : Q) :
    (x ⟶ y) ≃ {p : Quiver.Path x y // p.length = 1} where
  toFun a := ⟨a.toPath, rfl⟩
  invFun := arrowOfLengthOne
  left_inv := arrowOfLengthOne_toPath
  right_inv p := by
    apply Subtype.ext
    exact (lengthOnePath_eq_toPath p).symm

/-- Between distinct vertices, paths of length below two are exactly arrows. -/
def lowPathEquivLengthOnePath {x y : Q} (hxy : x ≠ y) :
    {p : Quiver.Path x y // p.length < 2} ≃
      {p : Quiver.Path x y // p.length = 1} where
  toFun p := ⟨p.1, by
    have hpos : 0 < p.1.length := by
      by_contra h
      have hzero : p.1.length = 0 := by omega
      exact hxy (p.1.eq_of_length_zero hzero)
    omega⟩
  invFun p := ⟨p.1, by omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At one vertex, paths of length below two are the trivial path or one
loop. -/
def optionArrowEquivLowPath (x : Q) :
    Option (x ⟶ x) ≃ {p : Quiver.Path x x // p.length < 2} where
  toFun
    | none => ⟨Quiver.Path.nil, by simp⟩
    | some a => ⟨a.toPath, by simp⟩
  invFun p :=
    if hzero : p.1.length = 0 then none
    else some (arrowOfLengthOne ⟨p.1, by omega⟩)
  left_inv a := by
    cases a with
    | none => simp
    | some a => simp [arrowOfLengthOne_toPath]
  right_inv p := by
    apply Subtype.ext
    by_cases hzero : p.1.length = 0
    · simp [p.1.eq_nil_of_length_zero hzero]
    · have hone : p.1.length = 1 := by omega
      simp only [hzero]
      exact (lengthOnePath_eq_toPath ⟨p.1, hone⟩).symm

/-- If all paths at or above `n` map into `W` and the shorter paths remain
linearly independent modulo `W`, then every element of the realization kernel
is supported in path lengths at least `n`. -/
theorem mem_lengthTail_of_map_eq_zero_of_low_independent
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {X Y : Category k Q}
    (W : Submodule k (F₀ (vertex X) ⟶ F₀ (vertex Y)))
    (n : ℕ)
    (hlong : ∀ p : Quiver.Path (vertex Y) (vertex X),
      n ≤ p.length → pathMap F₀ F₁ p ∈ W)
    (hlow : LinearIndependent k
      (fun p : {p : Quiver.Path (vertex Y) (vertex X) // p.length < n} ↦
        W.mkQ (pathMap F₀ F₁ p.1)))
    (f : X ⟶ Y)
    (hf : homMap F₀ F₁ X Y f = 0) :
    f ∈ lengthTail X Y n := by
  classical
  let coeff := homPathLinearEquiv X Y f
  let low := coeff.subtypeDomain (fun p ↦ p.length < n)
  have hquot' (g : Quiver.Path (vertex Y) (vertex X) →₀ k) :
      W.mkQ (homMap F₀ F₁ X Y ((homPathLinearEquiv X Y).symm g)) =
        Finsupp.linearCombination k
          (fun p : {p : Quiver.Path (vertex Y) (vertex X) // p.length < n} ↦
            W.mkQ (pathMap F₀ F₁ p.1))
          (g.subtypeDomain (fun p ↦ p.length < n)) := by
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g h hg hh =>
        simp only [map_add, Finsupp.subtypeDomain_add, hg, hh]
    | single p r =>
        by_cases hp : p.length < n
        · let q : {p : Quiver.Path (vertex Y) (vertex X) // p.length < n} :=
            ⟨p, hp⟩
          have hsub :
              (Finsupp.single p r).subtypeDomain (fun p ↦ p.length < n) =
                Finsupp.single q r := by
            ext a
            by_cases ha : a = q
            · subst a
              simp [q]
            · have hval : a.1 ≠ p := by
                intro h
                apply ha
                apply Subtype.ext
                exact h
              simp [Finsupp.subtypeDomain_apply, q, hval, Ne.symm ha]
          rw [hsub]
          simp [homPathLinearEquiv_symm_single, q]
        · have hmem := hlong p (le_of_not_gt hp)
          have hzero : W.mkQ (pathMap F₀ F₁ p) = 0 := by
            exact (Submodule.Quotient.mk_eq_zero W).mpr hmem
          have hsub :
              (Finsupp.single p r).subtypeDomain (fun p ↦ p.length < n) = 0 := by
            ext a
            have hval : a.1 ≠ p := by
              intro h
              exact hp (h ▸ a.2)
            simp [Finsupp.subtypeDomain_apply, hval]
          rw [hsub]
          simp [homPathLinearEquiv_symm_single, hzero]
  have hquot :
      W.mkQ (homMap F₀ F₁ X Y f) =
        Finsupp.linearCombination k
          (fun p : {p : Quiver.Path (vertex Y) (vertex X) // p.length < n} ↦
            W.mkQ (pathMap F₀ F₁ p.1)) low := by
    rw [← (homPathLinearEquiv X Y).symm_apply_apply f]
    exact hquot' coeff
  have hlowzero : low = 0 := by
    apply hlow
    rw [← hquot, hf, map_zero]
    simp
  rw [mem_lengthTail_iff]
  intro p hp
  by_contra hpn
  have hlt : p.length < n := Nat.lt_of_not_ge hpn
  have hpzero : coeff p = 0 :=
    (Finsupp.subtypeDomain_eq_zero_iff'.1 hlowzero) p hlt
  exact (Finsupp.mem_support_iff.mp hp) hpzero

end MagnitudeConjecture.LinearPathCategory
