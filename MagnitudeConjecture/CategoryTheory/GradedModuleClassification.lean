import MagnitudeConjecture.CategoryTheory.GradedModuleLocalEnd
import MagnitudeConjecture.CategoryTheory.GradedModuleShiftRigidity
import MagnitudeConjecture.Algebra.FiniteModuleDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-! # Graded classification from a complete gradable representative family -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u w
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- Forget the grading while retaining all ambient module maps. -/
def underlying : FiniteGradedModule.{u,u} R ⥤ ModuleCat.{u} A where
  obj X := X.module
  map f := ModuleCat.ofHom f

instance : (underlying (R := R)).Full where
  map_surjective f := ⟨f.hom, rfl⟩
instance : (underlying (R := R)).Faithful where
  map_injective h := congrArg ModuleCat.Hom.hom h
instance : (underlying (R := R)).Additive where
  map_add := by intros; rfl

/-- Ungraded indecomposability gives local ambient endomorphisms. -/
theorem underlyingLocal [FiniteDimensional k A] (X : FiniteGradedModule.{u,u} R)
    (hX : Indecomposable X.module) : IsLocalRing (End X) := by
  letI : IsLocalRing (End ((underlying (R := R)).obj X)) :=
    MagnitudeConjecture.moduleCat_end_isLocalRing (k := k) X.module hX
  exact RingEquiv.isLocalRing_noncomm
    (MagnitudeConjecture.CategoryTheory.Functor.endRingEquivOfFullyFaithful
      (underlying (R := R)) X).symm

/-- If every ungraded indecomposable has a graded representative, every graded
indecomposable is a shift of one of those representatives. The finite identity
decomposition is constructed from ordinary module decomposition. -/
theorem exists_iso_shift_of_complete_family [FiniteDimensional k A]
    {ι : Type w} (Y : ι → FiniteGradedModule.{u,u} R)
    (hY : ∀ i, Indecomposable (Y i).module)
    (hcomplete : ∀ M : ModuleCat.{u} A, Module.Finite k M → Indecomposable M →
      ∃ i, Nonempty (M ≅ (Y i).module))
    (X : FiniteGradedModule.{u,u} R)
    (hX : Indecomposable (⟨X, 0⟩ : ShiftedModule (R := R))) :
    ∃ i, ∃ s : ℤ, Nonempty ((⟨X, 0⟩ : ShiftedModule (R := R)) ≅ ⟨Y i, s⟩) := by
  classical
  obtain ⟨D⟩ := MagnitudeConjecture.finiteIndecomposableDecomposition_module_exists (k := k) X.module
  choose l hl using fun j ↦ hcomplete (D.summand j)
    (D.summand_finite (inferInstance : Module.Finite k X.module) j) (D.indecomposable j)
  let e (j : Fin D.n) := (hl j).some
  let p (j : Fin D.n) : X.module ⟶ (Y (l j)).module :=
    D.isoBiproduct.hom ≫ biproduct.π D.summand j ≫ (e j).hom
  let q (j : Fin D.n) : (Y (l j)).module ⟶ X.module :=
    (e j).inv ≫ biproduct.ι D.summand j ≫ D.isoBiproduct.inv
  have hs : ∑ j, p j ≫ q j = 𝟙 X.module := by
    calc
      _ = D.isoBiproduct.hom ≫ (∑ j, biproduct.π D.summand j ≫ biproduct.ι D.summand j) ≫
          D.isoBiproduct.inv := by
        simp only [p, q, Category.assoc, Iso.hom_inv_id_assoc,
          Preadditive.comp_sum, Preadditive.sum_comp]
      _ = _ := by rw [biproduct.total]; simp
  have hs' : ∑ j ∈ (Finset.univ : Finset (Fin D.n)),
      (p j).hom ≫ (q j).hom = 𝟙 X := by
    apply (underlying (R := R)).map_injective
    simp only [Functor.map_sum, Functor.map_comp, Functor.map_id]
    simpa [underlying] using hs
  obtain ⟨j, hj, d, hd⟩ := exists_iso_shift_of_decomposition Finset.univ X (fun j ↦ Y (l j))
    (fun j ↦ (p j).hom) (fun j ↦ (q j).hom) hs' hX (fun j _ ↦ underlyingLocal (Y (l j)) (hY (l j)))
  exact ⟨l j, -d, hd⟩

/-- For distinct ungraded representatives, a shifted isomorphism determines
both the representative label and the shift. -/
theorem label_shift_eq_of_iso {ι : Type w} (Y : ι → FiniteGradedModule.{u,u} R)
    (hY : ∀ i, Indecomposable (Y i).module)
    (hinj : ∀ i j, Nonempty ((Y i).module ≅ (Y j).module) → i = j)
    {i j : ι} {s t : ℤ}
    (e : (⟨Y i, s⟩ : ShiftedModule (R := R)) ≅ ⟨Y j, t⟩) : i = j ∧ s = t := by
  have hij := hinj i j ⟨(underlying (R := R)).mapIso (homGrading.forget.mapIso e)⟩
  subst j
  have hn : ¬ Subsingleton (Y i).module :=
    (not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp (hY i).1
  letI : Nontrivial (Y i).module := not_subsingleton_iff_nontrivial.mp hn
  exact ⟨rfl, shift_eq_of_iso (Y i) s t e⟩

end MagnitudeConjecture.Graded.FiniteGradedModule
