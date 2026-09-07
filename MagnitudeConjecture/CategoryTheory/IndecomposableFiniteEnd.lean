import MagnitudeConjecture.Algebra.IndecomposableLocalEnd
import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Local finite-dimensional endomorphism rings of indecomposable objects

In an idempotent-complete preadditive category, an idempotent endomorphism
splits the object as the biproduct of its image and complementary image.
Categorical indecomposability therefore makes every idempotent zero or one.
When the endomorphism algebra is finite-dimensional, the regular-module
Fitting criterion makes that algebra local.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory

universe u v uK

/-- An indecomposable object in an idempotent-complete preadditive category
has no nontrivial idempotent endomorphisms. -/
theorem indecomposable_idempotent_eq_zero_or_one
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [IsIdempotentComplete C]
    (X : C) (hX : Indecomposable X) (p : X ⟶ X)
    (hp : p ≫ p = p) : p = 0 ∨ p = 𝟙 X := by
  let q : X ⟶ X := 𝟙 X - p
  have hq : q ≫ q = q :=
    CategoryTheory.Idempotents.idem_of_id_sub_idem p hp
  obtain ⟨Y, i, e, hie, hei⟩ :=
    IsIdempotentComplete.idempotents_split X p hp
  obtain ⟨Z, j, r, hjr, hrj⟩ :=
    IsIdempotentComplete.idempotents_split X q hq
  letI : IsSplitEpi e := ⟨⟨SplitEpi.mk i hie⟩⟩
  letI : IsSplitMono i := ⟨⟨SplitMono.mk e hie⟩⟩
  letI : IsSplitEpi r := ⟨⟨SplitEpi.mk j hjr⟩⟩
  letI : IsSplitMono j := ⟨⟨SplitMono.mk r hjr⟩⟩
  have hpq : p ≫ q = 0 := by simp [q, hp]
  have hqp : q ≫ p = 0 := by simp [q, hp]
  have hir : i ≫ r = 0 := by
    apply (cancel_epi e).1
    apply (cancel_mono j).1
    rw [← Category.assoc, hei]
    simpa only [Category.assoc, hrj, comp_zero, zero_comp] using hpq
  have hje : j ≫ e = 0 := by
    apply (cancel_epi r).1
    apply (cancel_mono i).1
    rw [← Category.assoc, hrj]
    simpa only [Category.assoc, hei, comp_zero, zero_comp] using hqp
  let φ : X ≅ Y ⊞ Z :=
    { hom := biprod.lift e r
      inv := biprod.desc i j
      hom_inv_id := by
        simp [hei, hrj, q]
      inv_hom_id := by
        ext <;> simp [hie, hir, hjr, hje] }
  rcases hX.2 Y Z φ with hY | hZ
  · left
    have hi : i = 0 := hY.eq_of_src i 0
    simpa [hi] using hei.symm
  · right
    have hq0 : q = 0 := by
      have hj : j = 0 := hZ.eq_of_src j 0
      simpa [hj] using hrj.symm
    have hq0' : 𝟙 X - p = 0 := by simpa [q] using hq0
    exact (sub_eq_zero.mp hq0').symm

/-- If the endomorphism algebra of an indecomposable object is
finite-dimensional, then it is local. -/
theorem end_isLocalRing_of_finiteDimensional_indecomposable
    {k : Type uK} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [IsIdempotentComplete C]
    [CategoryTheory.Linear k C]
    (X : C) [FiniteDimensional k (End X)] (hX : Indecomposable X) :
    IsLocalRing (End X) := by
  have hone : (1 : End X) ≠ 0 := by
    change (𝟙 X : X ⟶ X) ≠ 0
    intro h
    exact hX.1 ((IsZero.iff_id_eq_zero X).2 h)
  letI : Nontrivial (End X) := ⟨⟨1, 0, hone⟩⟩
  apply finiteDimensional_isLocalRing_of_idempotents (k := k) (R := End X)
  intro f hf
  have hp : f.asHom ≫ f.asHom = f.asHom := by
    simpa only [End.mul_def] using congrArg End.asHom hf
  rcases indecomposable_idempotent_eq_zero_or_one X hX f.asHom hp with h | h
  · left
    apply End.ext
    change f.asHom = (0 : X ⟶ X)
    exact h
  · right
    apply End.ext
    change f.asHom = 𝟙 X
    exact h

end MagnitudeConjecture.CategoryTheory
