import MagnitudeConjecture.CategoryTheory.GradedModuleSupport
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The full category of graded modules supported in a finite interval -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- The interval condition as a property of objects in the graded category. -/
def intervalSupport (m : ℕ) : ObjectProperty (ShiftedModule.{u,u} (R := R)) :=
  SupportedIn m

abbrev SupportedCategory (m : ℕ) := (intervalSupport (R := R) m).FullSubcategory

/-- Taking the concrete graded product preserves interval support. -/
theorem supportedIn_sumObject {m : ℕ} {X Y : ShiftedModule.{u,u} (R := R)}
    (hX : SupportedIn m X) (hY : SupportedIn m Y) : SupportedIn m (sumObject X Y) := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  have hn := ((sumObject X Y).obj.grading.toVectorGrading.mem_support_iff j).mp hj
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  change z.1 ∈ X.obj.grading.component (j - X.degree) ∧
    z.2 ∈ Y.obj.grading.component (j - Y.degree) at hz
  have hmem {Z : ShiftedModule.{u,u} (R := R)} (x : Z.obj.module)
      (hx : x ∈ Z.obj.grading.component (j - Z.degree)) (hne : x ≠ 0) :
      j ∈ shiftedSupport Z := by
    apply Finset.mem_image.mpr
    refine ⟨j - Z.degree, (Z.obj.grading.toVectorGrading.mem_support_iff _).mpr ?_, by omega⟩
    intro he
    rw [he] at hx
    exact hne hx
  by_cases hx : z.1 = 0
  · have hy : z.2 ≠ 0 := by intro hy; exact hz0 (Prod.ext hx hy)
    simpa only [sumObject, add_zero] using hY j (hmem z.2 hz.2 hy)
  · simpa only [sumObject, add_zero] using hX j (hmem z.1 hz.1 hx)

/-- The interval subcategory has the same concrete binary sums as the ambient category. -/
def supportedSumBicone {m : ℕ} (X Y : SupportedCategory (R := R) m) : BinaryBicone X Y where
  pt := ⟨sumObject X.obj Y.obj, supportedIn_sumObject X.property Y.property⟩
  fst := ObjectProperty.homMk (sumBicone X.obj Y.obj).fst
  snd := ObjectProperty.homMk (sumBicone X.obj Y.obj).snd
  inl := ObjectProperty.homMk (sumBicone X.obj Y.obj).inl
  inr := ObjectProperty.homMk (sumBicone X.obj Y.obj).inr
  inl_fst := by apply ObjectProperty.hom_ext; exact (sumBicone X.obj Y.obj).inl_fst
  inl_snd := by apply ObjectProperty.hom_ext; exact (sumBicone X.obj Y.obj).inl_snd
  inr_fst := by apply ObjectProperty.hom_ext; exact (sumBicone X.obj Y.obj).inr_fst
  inr_snd := by apply ObjectProperty.hom_ext; exact (sumBicone X.obj Y.obj).inr_snd

instance (m : ℕ) : HasBinaryBiproducts (SupportedCategory (R := R) m) where
  has_binary_biproduct X Y := hasBinaryBiproduct_of_total (supportedSumBicone X Y) (by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (add_zero x.1) (zero_add x.2))

instance (m : ℕ) : HasZeroObject (SupportedCategory (R := R) m) := by
  let Z : SupportedCategory (R := R) m := ⟨⟨zeroObject, 0⟩, by
    intro d hd
    obtain ⟨j, hj, _⟩ := Finset.mem_image.mp hd
    have hn := ((zeroObject (R := R)).grading.toVectorGrading.mem_support_iff j).mp hj
    exact (hn rfl).elim⟩
  apply IsZero.hasZeroObject (X := Z)
  apply (IsZero.iff_id_eq_zero _).2
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim (α := PUnit) _ _

instance (m : ℕ) : HasFiniteBiproducts (SupportedCategory (R := R) m) := by
  let : HasFiniteProducts (SupportedCategory (R := R) m) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Interval support cannot hide a nontrivial direct-sum decomposition. -/
theorem supported_indecomposable_iff {m : ℕ} (X : SupportedCategory (R := R) m) :
    Indecomposable X ↔ Indecomposable X.obj := by
  let F := (intervalSupport (R := R) m).ι
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  constructor
  · intro hX
    constructor
    · intro hz
      exact hX.1 (IsZero.of_full_of_faithful_of_isZero F X hz)
    · intro Y Z e
      have hY : SupportedIn m Y := supportedIn_of_splitMono (biprod.inl ≫ e.inv) X.property
      have hZ : SupportedIn m Z := supportedIn_of_splitMono (biprod.inr ≫ e.inv) X.property
      let Y' : SupportedCategory (R := R) m := ⟨Y, hY⟩
      let Z' : SupportedCategory (R := R) m := ⟨Z, hZ⟩
      let e' : X ≅ Y' ⊞ Z' := F.preimageIso (e ≪≫ (F.mapBiprod Y' Z').symm)
      rcases hX.2 Y' Z' e' with hy | hz
      · exact Or.inl (F.map_isZero hy)
      · exact Or.inr (F.map_isZero hz)
  · exact MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive F X

/-- An ambient finite indecomposable decomposition stays inside the support interval. -/
theorem supported_finiteDecomposition {m : ℕ} (X : SupportedCategory (R := R) m) :
    Nonempty (MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X) := by
  classical
  obtain ⟨d⟩ := finiteDecomposition X.obj
  let F := (intervalSupport (R := R) m).ι
  let L (i : Fin d.n) : SupportedCategory (R := R) m :=
    ⟨d.summand i, supportedIn_of_splitMono (biproduct.ι d.summand i ≫ d.isoBiproduct.inv)
      X.property⟩
  exact ⟨{ n := d.n
           summand := L
           indecomposable := fun i ↦ (supported_indecomposable_iff (L i)).mpr (d.indecomposable i)
           isoBiproduct := F.preimageIso (d.isoBiproduct ≪≫ (F.mapBiproduct L).symm) }⟩

end MagnitudeConjecture.Graded.FiniteGradedModule
