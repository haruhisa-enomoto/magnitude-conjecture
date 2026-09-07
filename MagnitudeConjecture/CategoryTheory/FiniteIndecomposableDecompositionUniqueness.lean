import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import Mathlib.Logic.Equiv.Fin.Basic
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaKrullSchmidtNormalForm

/-!
# Uniqueness of the size of finite indecomposable decompositions

In an idempotent-complete preadditive category, finite decompositions into
indecomposables with local endomorphism rings have a well-defined number of
summands.  Only the cardinal consequence of Krull--Schmidt uniqueness is
recorded here; no global finite skeleton is required.

The cancellation argument is the label-free specialization of the finite
Krull--Schmidt proof in the vendored Iyama cone.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.Iyama

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]

/-- A retraction of an indecomposable object from a finite biproduct of
indecomposables has an invertible coordinate when the source endomorphism
ring is local. -/
theorem exists_isIso_component_of_retraction_finBiproduct
    [IsIdempotentComplete C]
    {X : C} (hX : Indecomposable X) (hlocal : IsLocalRing (End X))
    (n : ℕ) (Y : Fin n → C) (hY : ∀ i, Indecomposable (Y i))
    (f : X ⟶ ⨁ Y) (g : (⨁ Y) ⟶ X)
    (hfg : f ≫ g = 𝟙 X) :
    ∃ i : Fin n, IsIso (f ≫ biproduct.π Y i) := by
  classical
  let c : Fin n → End X := fun i ↦
    ((f ≫ biproduct.π Y i) ≫ (biproduct.ι Y i ≫ g) : End X)
  have hsum : ∑ i : Fin n, c i = 𝟙 X := by
    change
      ∑ i : Fin n,
          ((f ≫ biproduct.π Y i) ≫ (biproduct.ι Y i ≫ g) : End X) =
        (𝟙 X : End X)
    calc
      ∑ i : Fin n,
          ((f ≫ biproduct.π Y i) ≫ (biproduct.ι Y i ≫ g) : End X) =
          f ≫ (∑ i : Fin n, biproduct.π Y i ≫ biproduct.ι Y i) ≫ g := by
            simp only [Category.assoc, Preadditive.comp_sum,
              Preadditive.sum_comp]
      _ = f ≫ g := by rw [biproduct.total]; simp
      _ = 𝟙 X := hfg
  letI : IsLocalRing (End X) := hlocal
  have hunit : IsUnit (∑ i : Fin n, c i) := by
    rw [hsum]
    exact isUnit_one
  obtain ⟨i, _, hi⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := c) hunit
  let a : X ⟶ Y i := f ≫ biproduct.π Y i
  let b : Y i ⟶ X := biproduct.ι Y i ≫ g
  have habI : IsIso (a ≫ b) := by
    apply (isUnit_iff_isIso (a ≫ b)).1
    simpa only [c, a, b] using hi
  letI : IsIso (a ≫ b) := habI
  letI : IsSplitMono a := IsSplitMono.mk'
    { retraction := b ≫ inv (a ≫ b)
      id := by rw [← Category.assoc, IsIso.hom_inv_id] }
  have ha : IsIso a :=
    isIso_of_isSplitMono_to_indecomposable (hY i) a hX.1
  exact ⟨i, by simpa only [a] using ha⟩

/-- Two finite biproducts of indecomposables with local endomorphism rings
can be isomorphic only when their index types have the same cardinality. -/
theorem eq_of_nonempty_iso_finBiproduct_of_indec_local
    [IsIdempotentComplete C] :
    ∀ (n m : ℕ) (X : Fin n → C) (Y : Fin m → C),
      (∀ i, Indecomposable (X i)) →
      (∀ i, IsLocalRing (End (X i))) →
      (∀ j, Indecomposable (Y j)) →
      Nonempty ((⨁ X) ≅ ⨁ Y) → n = m := by
  intro n
  induction n with
  | zero =>
      intro m X Y hX hlocal hY e
      cases m with
      | zero => rfl
      | succ m =>
          obtain ⟨e⟩ := e
          have hzeroSource : IsZero (⨁ X) := by
            rw [IsZero.iff_id_eq_zero]
            apply biproduct.hom_ext
            intro i
            exact Fin.elim0 i
          have hzeroTarget : IsZero (⨁ Y) := hzeroSource.of_iso e.symm
          have hzeroHead : IsZero (Y 0) := by
            rw [IsZero.iff_id_eq_zero]
            calc
              𝟙 (Y 0) = biproduct.ι Y 0 ≫ biproduct.π Y 0 := by simp
              _ = 0 := by
                rw [hzeroTarget.eq_of_tgt (biproduct.ι Y 0) 0, zero_comp]
          exact (hY 0).1 hzeroHead |>.elim
  | succ n ih =>
      intro m X Y hX hlocal hY e
      cases m with
      | zero =>
          obtain ⟨e⟩ := e
          have hzeroTarget : IsZero (⨁ Y) := by
            rw [IsZero.iff_id_eq_zero]
            apply biproduct.hom_ext
            intro j
            exact Fin.elim0 j
          have hzeroSource : IsZero (⨁ X) := hzeroTarget.of_iso e
          have hzeroHead : IsZero (X 0) := by
            rw [IsZero.iff_id_eq_zero]
            calc
              𝟙 (X 0) = biproduct.ι X 0 ≫ biproduct.π X 0 := by simp
              _ = 0 := by
                rw [hzeroSource.eq_of_tgt (biproduct.ι X 0) 0, zero_comp]
          exact (hX 0).1 hzeroHead |>.elim
      | succ m =>
          obtain ⟨e⟩ := e
          let f : X 0 ⟶ ⨁ Y := biproduct.ι X 0 ≫ e.hom
          let g : (⨁ Y) ⟶ X 0 := e.inv ≫ biproduct.π X 0
          have hfg : f ≫ g = 𝟙 (X 0) := by
            simp [f, g, Category.assoc]
          obtain ⟨j, hj⟩ :=
            exists_isIso_component_of_retraction_finBiproduct
              (hX 0) (hlocal 0) (m + 1) Y hY f g hfg
          let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 j
          let eReindex : (⨁ fun k ↦ Y (σ k)) ≅ ⨁ Y :=
            biproduct.whiskerEquiv σ (fun _ ↦ Iso.refl _)
          let eBinary :
              X 0 ⊞ (⨁ fun i : Fin n ↦ X i.succ) ≅
                Y (σ 0) ⊞ (⨁ fun k : Fin m ↦ Y (σ k.succ)) :=
            (finBiproductConsIso X).symm.trans
              (e.trans
                (eReindex.symm.trans
                  (finBiproductConsIso (fun k ↦ Y (σ k)))))
          have htop : IsIso
              (biprod.inl ≫ eBinary.hom ≫ biprod.fst) := by
            have hcomponent := hj
            change IsIso (f ≫ biproduct.π Y j) at hcomponent
            have hσ0 : σ 0 = j := by simp [σ]
            have hcomponent' : IsIso (f ≫ biproduct.π Y (σ 0)) := by
              rw [hσ0]
              exact hcomponent
            have hsourceHead :
                biprod.inl ≫ (finBiproductConsIso X).symm.hom =
                  biproduct.ι X 0 := by
              dsimp only [finBiproductConsIso]
              simp
            have htargetHead :
                eReindex.symm.hom ≫
                    (finBiproductConsIso (fun k ↦ Y (σ k))).hom ≫
                      biprod.fst =
                  biproduct.π Y (σ 0) := by
              dsimp only [finBiproductConsIso]
              rw [biprod.lift_fst]
              dsimp only [eReindex]
              change
                (biproduct.whiskerEquiv σ
                    (fun x ↦ Iso.refl (Y (σ x)))).inv ≫
                    biproduct.π (fun k ↦ Y (σ k)) 0 =
                  biproduct.π Y (σ 0)
              rw [biproduct.whiskerEquiv_inv_eq_lift]
              simp
            have heq :
                biprod.inl ≫ eBinary.hom ≫ biprod.fst =
                  f ≫ biproduct.π Y (σ 0) := by
              dsimp only [eBinary]
              simp only [Iso.trans_hom, Category.assoc]
              rw [← Category.assoc, hsourceHead]
              rw [htargetHead]
              dsimp only [f]
              exact (Category.assoc _ _ _).symm
            rw [heq]
            exact hcomponent'
          letI : IsIso (biprod.inl ≫ eBinary.hom ≫ biprod.fst) := htop
          let eTail :
              (⨁ fun i : Fin n ↦ X i.succ) ≅
                ⨁ fun k : Fin m ↦ Y (σ k.succ) :=
            Biprod.isoElim eBinary
          have hnm : n = m :=
            ih m (fun i ↦ X i.succ) (fun k ↦ Y (σ k.succ))
              (fun i ↦ hX i.succ) (fun i ↦ hlocal i.succ)
              (fun k ↦ hY (σ k.succ)) ⟨eTail⟩
          exact congrArg Nat.succ hnm

/-- The number of summands in a displayed finite indecomposable
decomposition is invariant under isomorphism. -/
theorem FiniteIndecomposableDecomposition.n_eq_of_iso
    [IsIdempotentComplete C]
    {X Y : C} (dX : FiniteIndecomposableDecomposition X)
    (dY : FiniteIndecomposableDecomposition Y)
    (hlocal : ∀ i, IsLocalRing (End (dX.summand i)))
    (e : X ≅ Y) : dX.n = dY.n := by
  apply eq_of_nonempty_iso_finBiproduct_of_indec_local
    dX.n dY.n dX.summand dY.summand dX.indecomposable hlocal
      dY.indecomposable
  exact ⟨dX.isoBiproduct.symm ≪≫ e ≪≫ dY.isoBiproduct⟩

end MagnitudeConjecture.CategoryTheory
