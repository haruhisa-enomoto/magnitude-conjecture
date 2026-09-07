import MagnitudeConjecture.Algebra.StringWord
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Positive ordinary paths as string words

The positive embedding of the displayed quiver into its symmetrification is
injective on paths.  Moreover, an ordinary path which survives the relation
quotient is a string when every arrow is read positively.  The latter fact
uses ordinary path factorization: a positive signed subpath of a positive
path is an ordinary subpath, so a killed subpath would kill the whole path.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The positive embedding of the displayed quiver is injective on paths. -/
theorem positivePath_injective {x y : Q}
    (p q : Quiver.Path x y) (h : positivePath p = positivePath q) :
    p = q := by
  induction hlength : p.length using Nat.strong_induction_on
      generalizing x y q with
  | h n ih =>
    cases p with
    | nil =>
        have hlen := congrArg Quiver.Path.length h
        rw [positivePath_length, positivePath_length] at hlen
        exact (q.eq_nil_of_length_zero hlen.symm).symm
    | @cons z y p a =>
        cases q with
        | nil =>
            have hlen := congrArg Quiver.Path.length h
            simp only [positivePath_length, Quiver.Path.length_cons,
              Quiver.Path.length_nil] at hlen
            omega
        | @cons w y q b =>
            have hpqlength : p.length = q.length := by
              have htotal := congrArg Quiver.Path.length h
              simp only [positivePath_length,
                Quiver.Path.length_cons] at htotal
              omega
            have hcomp :
                (positivePath p).comp (positivePath a.toPath) =
                  (positivePath q).comp (positivePath b.toPath) := by
              simpa only [positivePath_cons] using h
            obtain ⟨hzw, hpq, hab⟩ :=
              path_comp_decomposition_unique hcomp (by
                simpa only [positivePath_length] using hpqlength)
            cases hzw
            have hpq' : p = q :=
              ih p.length (by
                simp only [Quiver.Path.length_cons] at hlength
                omega) p q hpq.eq rfl
            subst q
            have hab' : (positiveArrow a).toPath =
                (positiveArrow b).toPath := by
              simpa only [positivePath_toPath] using hab.eq
            have hsigned : positiveArrow a = positiveArrow b :=
              (Quiver.Path.hom_heq_of_cons_eq_cons hab').eq
            have : a = b := Sum.inl.inj hsigned
            subst b
            rfl

/-- Every positive ordinary subpath of a surviving positive path also
survives the relation quotient. -/
theorem avoidsRelations_positivePath_of_pathMap_ne_zero
    {x y : Q} (p : Quiver.Path x y) (hp : pathMap R p ≠ 0) :
    AvoidsRelations R (positivePath p) := by
  intro a b q hq
  rcases hq with ⟨l, r, hfactor⟩
  have hlq : l.length + q.length ≤ p.length := by
    have hlength := congrArg Quiver.Path.length hfactor
    simp only [Quiver.Path.length_comp, positivePath_length] at hlength
    omega
  obtain ⟨z, p₁, tail, hpfactor, hp₁⟩ :=
    p.exists_eq_comp_of_le_length
      (Nat.le_trans (Nat.le_add_right _ _) hlq)
  have hcomp₁ : l.comp ((positivePath q).comp r) =
      (positivePath p₁).comp (positivePath tail) := by
    rw [← positivePath_comp, ← hpfactor]
    exact hfactor.symm
  obtain ⟨hz, _, hsuffix⟩ :=
    path_comp_decomposition_unique hcomp₁ (by
      simpa only [positivePath_length] using hp₁.symm)
  cases hz
  have htail : (positivePath q).comp r = positivePath tail :=
    hsuffix.eq
  have hqle : q.length ≤ tail.length := by
    have hlength := congrArg Quiver.Path.length htail
    simp only [Quiver.Path.length_comp, positivePath_length] at hlength
    omega
  obtain ⟨w, q', rest, htail', hq'⟩ :=
    tail.exists_eq_comp_of_le_length hqle
  have hcomp₂ : (positivePath q).comp r =
      (positivePath q').comp (positivePath rest) := by
    rw [← positivePath_comp, ← htail']
    exact htail
  obtain ⟨hw, hqq', _⟩ :=
    path_comp_decomposition_unique hcomp₂ (by
      simpa only [positivePath_length] using hq'.symm)
  cases hw
  have hqq : q = q' := positivePath_injective q q' hqq'.eq
  subst q'
  have hordinary : p = p₁.comp (q.comp rest) := by
    rw [hpfactor, htail']
  intro hqzero
  apply hp
  calc
    pathMap R p = pathMap R (p₁.comp (q.comp rest)) := by
      rw [hordinary]
    _ = pathMap R (q.comp rest) ≫ pathMap R p₁ :=
      (pathMap_comp R p₁ (q.comp rest)).symm
    _ = (pathMap R rest ≫ pathMap R q) ≫ pathMap R p₁ :=
      congrArg (fun f ↦ f ≫ pathMap R p₁)
        (pathMap_comp R q rest).symm
    _ = 0 := by
      rw [hqzero, CategoryTheory.Limits.comp_zero,
        CategoryTheory.Limits.zero_comp]

/-- A path containing only positive signed letters is reduced. -/
theorem isReduced_positivePath {x y : Q} (p : Quiver.Path x y) :
    IsReduced (positivePath p) := by
  intro a b e hsub
  cases e with
  | inl e =>
      apply not_negativeArrow_contiguousSubpath_positivePath e p
      apply (show IsContiguousSubpath (negativeArrow e).toPath
          ((positiveArrow e).toPath.comp
            (negativeArrow e).toPath) from ?_).trans hsub
      refine ⟨(positiveArrow e).toPath, Quiver.Path.nil, ?_⟩
      simp
  | inr e =>
      apply not_negativeArrow_contiguousSubpath_positivePath e p
      apply (show IsContiguousSubpath (negativeArrow e).toPath
          ((negativeArrow e).toPath.comp
            (positiveArrow e).toPath) from ?_).trans hsub
      refine ⟨Quiver.Path.nil, (positiveArrow e).toPath, ?_⟩
      rfl

/-- The reverse of a positive path contains no nontrivial positive ordinary
subpath. -/
theorem avoidsRelations_reverse_positivePath
    (hR : IsAdmissible R) {x y : Q} (p : Quiver.Path x y) :
    AvoidsRelations R (positivePath p).reverse := by
  intro a b q hq
  by_cases hzero : q.length = 0
  · apply pathMap_ne_zero_of_length_lt_two hR q
    omega
  · exfalso
    obtain ⟨z, e, tail, _, hqpath⟩ :=
      q.eq_toPath_comp_of_length_eq_succ (show q.length =
          (q.length - 1) + 1 by omega)
    apply not_negativeArrow_contiguousSubpath_positivePath e p
    have hreverse : IsContiguousSubpath
        (positivePath q).reverse (positivePath p) :=
      (isContiguousSubpath_reverse_iff
        (positivePath q).reverse (positivePath p)).1 (by
          simpa only [Quiver.Path.reverse_reverse] using hq)
    apply (show IsContiguousSubpath (negativeArrow e).toPath
        (positivePath q).reverse from ?_).trans hreverse
    refine ⟨(positivePath tail).reverse, Quiver.Path.nil, ?_⟩
    calc
      (positivePath q).reverse =
          (positivePath tail).reverse.comp
            (positiveArrow e).toPath.reverse := by
        rw [hqpath, positivePath_comp, positivePath_toPath,
          Quiver.Path.reverse_comp]
      _ = (positivePath tail).reverse.comp
          ((negativeArrow e).toPath.comp Quiver.Path.nil) := by
        simp only [Quiver.Path.comp_nil, Quiver.Path.reverse_toPath]
        rfl

/-- A surviving ordinary path, read entirely positively, is a string. -/
theorem isString_positivePath_of_pathMap_ne_zero
    (hR : IsAdmissible R) {x y : Q} (p : Quiver.Path x y)
    (hp : pathMap R p ≠ 0) : IsString R (positivePath p) :=
  ⟨isReduced_positivePath p,
    avoidsRelations_positivePath_of_pathMap_ne_zero p hp,
    avoidsRelations_reverse_positivePath hR p⟩

end MagnitudeConjecture.BoundQuiver.StringWord
