import MagnitudeConjecture.CategoryTheory.MeshCovering
import Mathlib.CategoryTheory.Category.Quiv

/-!
# Stable polarized translation quivers

When the projective boundary is empty and the translation is bijective, the
polarization makes translation into an automorphism of the underlying quiver.
On arrows, this is the composite of two successive polarized mesh pairings.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u v

variable {Q : Type u} [Quiver.{v} Q]
variable (T : RightMeshData Q)

/-- A vertex regarded as nonprojective when the projective boundary is empty. -/
def stableNonprojective (hstable : T.projective = ∅) (x : Q) :
    {x : Q // x ∉ T.projective} :=
  ⟨x, by simp [hstable]⟩

/-- Translation as a total self-map on a stable right translation quiver. -/
def stableTau (hstable : T.projective = ∅) (x : Q) : Q :=
  T.tau (T.stableNonprojective hstable x)

/-- Total stable translation, packaged as an equivalence. -/
def stableTauEquiv (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable)) : Q ≃ Q :=
  Equiv.ofBijective (T.stableTau hstable) hbijective

@[simp]
theorem stableTauEquiv_apply (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable)) (x : Q) :
    T.stableTauEquiv hstable hbijective x = T.stableTau hstable x :=
  rfl

/-- Two successive polarized arrow pairings translate both endpoints. -/
def stableArrowEquiv (hstable : T.projective = ∅) (x y : Q) :
    (x ⟶ y) ≃ (T.stableTau hstable x ⟶ T.stableTau hstable y) :=
  (T.arrowEquiv (T.stableNonprojective hstable x) y).trans
    (T.arrowEquiv (T.stableNonprojective hstable y)
      (T.stableTau hstable x))

/-- Stable translation as an automorphism of the underlying quiver. -/
def stableTauQuiverIso (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable)) :
    CategoryTheory.Quiv.of Q ≅ CategoryTheory.Quiv.of Q :=
  CategoryTheory.Quiv.isoOfEquiv
    (T.stableTauEquiv hstable hbijective)
    (T.stableArrowEquiv hstable)

/-- Stable translation as an element of the quiver-automorphism group. -/
abbrev stableTauQuiverAut (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable)) :
    CategoryTheory.Aut (CategoryTheory.Quiv.of Q) :=
  T.stableTauQuiverIso hstable hbijective

@[simp]
theorem stableTauQuiverIso_hom_obj (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable)) (x : Q) :
    (T.stableTauQuiverIso hstable hbijective).hom.obj x =
      T.stableTau hstable x :=
  rfl

@[simp]
theorem stableTauQuiverIso_hom_map (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable))
    {x y : Q} (a : x ⟶ y) :
    (T.stableTauQuiverIso hstable hbijective).hom.map a =
      T.stableArrowEquiv hstable x y a :=
  rfl

/-- Stable translation commutes with one polarized arrow pairing. -/
theorem stableTauQuiverAut_map_arrowEquiv
    (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable))
    {x y : Q} (a : x ⟶ y) :
    (T.stableTauQuiverAut hstable hbijective).hom.map
        ((T.arrowEquiv (T.stableNonprojective hstable x) y) a) =
      (T.arrowEquiv
        (T.stableNonprojective hstable (T.stableTau hstable x))
        (T.stableTau hstable y))
        ((T.stableTauQuiverAut hstable hbijective).hom.map a) := by
  rfl

/-- The total space of arrows of a quiver, including both endpoints. -/
abbrev TotalArrow (Q : Type u) [Quiver.{v} Q] :=
  Σ x y : Q, x ⟶ y

/-- A quiver automorphism acts on the total space of arrows. -/
def quiverIsoTotalArrowEquiv
    (E : CategoryTheory.Quiv.of Q ≅ CategoryTheory.Quiv.of Q) :
    TotalArrow Q ≃ TotalArrow Q :=
  Equiv.sigmaCongr (CategoryTheory.Quiv.equivOfIso E)
    (fun _ ↦ Equiv.sigmaCongr (CategoryTheory.Quiv.equivOfIso E)
      (fun _ ↦ CategoryTheory.Quiv.homEquivOfIso E))

@[simp]
theorem quiverIsoTotalArrowEquiv_apply
    (E : CategoryTheory.Quiv.of Q ≅ CategoryTheory.Quiv.of Q)
    {x y : Q} (a : x ⟶ y) :
    quiverIsoTotalArrowEquiv E ⟨x, y, a⟩ =
      ⟨E.hom.obj x, E.hom.obj y, E.hom.map a⟩ :=
  rfl

/-- The action on total arrows is multiplicative. -/
def quiverAutTotalArrowAction :
    CategoryTheory.Aut (CategoryTheory.Quiv.of Q) →*
      Equiv.Perm (TotalArrow Q) where
  toFun E := quiverIsoTotalArrowEquiv E
  map_one' := by
    apply Equiv.ext
    rintro ⟨x, y, a⟩
    rw [quiverIsoTotalArrowEquiv_apply]
    rfl
  map_mul' E F := by
    apply Equiv.ext
    rintro ⟨x, y, a⟩
    rw [quiverIsoTotalArrowEquiv_apply]
    change ⟨(E * F).hom.obj x, (E * F).hom.obj y,
      (E * F).hom.map a⟩ =
        quiverIsoTotalArrowEquiv E (quiverIsoTotalArrowEquiv F ⟨x, y, a⟩)
    rw [quiverIsoTotalArrowEquiv_apply, quiverIsoTotalArrowEquiv_apply]
    rfl

@[simp]
theorem quiverAutTotalArrowAction_apply
    (E : CategoryTheory.Aut (CategoryTheory.Quiv.of Q))
    {x y : Q} (a : x ⟶ y) :
    quiverAutTotalArrowAction (Q := Q) E ⟨x, y, a⟩ =
      ⟨E.hom.obj x, E.hom.obj y, E.hom.map a⟩ :=
  quiverIsoTotalArrowEquiv_apply E a

/-- Polarization as a self-map of the total arrow space. -/
def stablePolarizationTotal (hstable : T.projective = ∅)
    (A : TotalArrow Q) : TotalArrow Q := by
  rcases A with ⟨x, y, a⟩
  exact ⟨y, T.stableTau hstable x,
    (T.arrowEquiv (T.stableNonprojective hstable x) y) a⟩

theorem stableTau_totalArrow_commute
    (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable))
    (A : TotalArrow Q) :
    quiverAutTotalArrowAction (Q := Q)
        (T.stableTauQuiverAut hstable hbijective)
        (T.stablePolarizationTotal hstable A) =
      T.stablePolarizationTotal hstable
        (quiverAutTotalArrowAction (Q := Q)
          (T.stableTauQuiverAut hstable hbijective) A) := by
  rcases A with ⟨x, y, a⟩
  rw [quiverAutTotalArrowAction_apply, quiverAutTotalArrowAction_apply]
  dsimp only [stablePolarizationTotal]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · rfl
    · exact heq_of_eq
        (T.stableTauQuiverAut_map_arrowEquiv hstable hbijective a)

private theorem perm_zpow_apply_commute
    {X : Type*} (f : Equiv.Perm X) (p : X → X)
    (h : ∀ x, f (p x) = p (f x)) (n : ℤ) (x : X) :
    (f ^ n) (p x) = p ((f ^ n) x) := by
  have hinv : ∀ x, f⁻¹ (p x) = p (f⁻¹ x) := by
    intro x
    apply f.injective
    simpa using (h (f⁻¹ x)).symm
  induction n using Int.induction_on generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n + (1 : ℤ) by rfl, zpow_add]
      change (f ^ n) (f (p x)) = p ((f ^ n) (f x))
      rw [h]
      simpa only [zpow_natCast] using ih (f x)
  | pred n ih =>
      rw [show -(n : ℤ) - 1 = -(n : ℤ) + (-1 : ℤ) by omega, zpow_add]
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      simp only [zpow_neg_one]
      rw [hinv]
      exact ih (f⁻¹ x)

/-- Every integer power of stable translation commutes with polarization on
the total arrow space. -/
theorem stableTau_zpow_totalArrow_commute
    (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable))
    (n : ℤ) (A : TotalArrow Q) :
    quiverAutTotalArrowAction (Q := Q)
        ((T.stableTauQuiverAut hstable hbijective) ^ n)
        (T.stablePolarizationTotal hstable A) =
      T.stablePolarizationTotal hstable
        (quiverAutTotalArrowAction (Q := Q)
          ((T.stableTauQuiverAut hstable hbijective) ^ n) A) := by
  rw [map_zpow]
  exact perm_zpow_apply_commute
    (quiverAutTotalArrowAction (Q := Q)
      (T.stableTauQuiverAut hstable hbijective))
    (T.stablePolarizationTotal hstable)
    (T.stableTau_totalArrow_commute hstable hbijective) n A

/-- Integer powers of stable translation commute with translation on
vertices. -/
theorem stableTau_zpow_obj_tau
    (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable))
    (n : ℤ) (x : Q) :
    ((T.stableTauQuiverAut hstable hbijective) ^ n).hom.obj
        (T.stableTau hstable x) =
      T.stableTau hstable
        (((T.stableTauQuiverAut hstable hbijective) ^ n).hom.obj x) := by
  calc
    ((T.stableTauQuiverAut hstable hbijective) ^ n).hom.obj
        (T.stableTau hstable x) =
      ((T.stableTauQuiverAut hstable hbijective) ^ (n + 1)).hom.obj x := by
        rw [zpow_add]
        rfl
    _ = ((T.stableTauQuiverAut hstable hbijective) ^ (1 + n)).hom.obj x := by
      rw [add_comm]
    _ = T.stableTau hstable
        (((T.stableTauQuiverAut hstable hbijective) ^ n).hom.obj x) := by
      rw [zpow_add]
      rfl

/-- Integer powers of stable translation commute with the chosen
polarization, with the translated endpoint made explicit. -/
theorem stableTau_zpow_map_arrowEquiv
    (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable))
    (n : ℤ) {x y : Q} (a : x ⟶ y) :
    (((T.stableTauQuiverAut hstable hbijective) ^ n).hom.map
      ((T.arrowEquiv (T.stableNonprojective hstable x) y) a)).cast rfl
        (T.stableTau_zpow_obj_tau hstable hbijective n x) =
      (T.arrowEquiv
        (T.stableNonprojective hstable
          (((T.stableTauQuiverAut hstable hbijective) ^ n).hom.obj x))
        (((T.stableTauQuiverAut hstable hbijective) ^ n).hom.obj y))
        (((T.stableTauQuiverAut hstable hbijective) ^ n).hom.map a) := by
  have htotal := T.stableTau_zpow_totalArrow_commute
    hstable hbijective n (⟨x, y, a⟩ : TotalArrow Q)
  rw [quiverAutTotalArrowAction_apply,
    quiverAutTotalArrowAction_apply] at htotal
  dsimp only [stablePolarizationTotal] at htotal
  rw [Quiver.Hom.cast_eq_iff_heq]
  exact (Sigma.ext_iff.mp (eq_of_heq (Sigma.ext_iff.mp htotal).2)).2

/-- In a stable translation quiver with bijective translation, polarization
identifies the incoming costar and outgoing star at a vertex. -/
def stableCostarStarEquiv
    (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable)) (y : Q) :
    Quiver.Costar y ≃ Quiver.Star y :=
  Equiv.sigmaCongr (T.stableTauEquiv hstable hbijective)
    (fun x ↦ T.arrowEquiv (T.stableNonprojective hstable x) y)

@[simp]
theorem stableCostarStarEquiv_apply
    (hstable : T.projective = ∅)
    (hbijective : Function.Bijective (T.stableTau hstable))
    (y : Q) (A : Quiver.Costar y) :
    T.stableCostarStarEquiv hstable hbijective y A =
      ⟨T.stableTau hstable A.1,
        (T.arrowEquiv (T.stableNonprojective hstable A.1) y) A.2⟩ :=
  rfl

end MagnitudeConjecture.MeshCategory.RightMeshData
