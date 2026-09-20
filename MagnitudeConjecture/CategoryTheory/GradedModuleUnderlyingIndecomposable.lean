import MagnitudeConjecture.CategoryTheory.GradedModuleClassification

/-! # Underlying indecomposability implies graded indecomposability -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- A grading and any shift of it preserve indecomposability of an underlying module. -/
theorem indecomposable_of_underlying (X : FiniteGradedModule.{u,u} R) (s : ℤ)
    (hX : Indecomposable X.module) :
    Indecomposable (⟨X, s⟩ : ShiftedModule (R := R)) := by
  let F : ShiftedModule (R := R) ⥤ ModuleCat A := homGrading.forget ⋙ underlying
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have reflectZero (Y : ShiftedModule (R := R)) (hY : IsZero (F.obj Y)) : IsZero Y := by
    apply (IsZero.iff_id_eq_zero Y).2
    apply F.map_injective
    simpa only [F.map_id, F.map_zero] using hY.eq_of_src (𝟙 (F.obj Y)) 0
  constructor
  · intro hz
    exact hX.1 (F.map_isZero hz)
  · intro Y Z e
    let e' := F.mapIso e ≪≫ F.mapBiprod Y Z
    rcases hX.2 (F.obj Y) (F.obj Z) e' with hY | hZ
    · exact Or.inl (reflectZero Y hY)
    · exact Or.inr (reflectZero Z hZ)

end MagnitudeConjecture.Graded.FiniteGradedModule
