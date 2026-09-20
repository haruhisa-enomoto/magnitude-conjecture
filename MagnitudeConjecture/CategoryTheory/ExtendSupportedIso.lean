import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Extending a natural isomorphism between functors that vanish off a full image -/
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits
namespace MagnitudeConjecture
universe u₁ u₂ u₃ v₁ v₂ v₃
variable {D : Type u₁} {C : Type u₂} {E : Type u₃}
variable [Category.{v₁} D] [Category.{v₂} C] [Category.{v₃} E]
variable (I : D ⥤ C) (hI : Function.Injective I.obj)
variable (F G : C ⥤ E) (α : I ⋙ F ≅ I ⋙ G)
variable (hF : ∀ c, c ∉ Set.range I.obj → IsZero (F.obj c))
variable (hG : ∀ c, c ∉ Set.range I.obj → IsZero (G.obj c))

/-- Use the prescribed comparison on the image and the unique zero comparison elsewhere. -/
def supportedExtensionIsoAt (c : C) : F.obj c ≅ G.obj c := by
  classical
  exact if h : c ∈ Set.range I.obj then
    (eqToIso (congrArg F.obj (Classical.choose_spec h))).symm ≪≫
      α.app (Classical.choose h) ≪≫ eqToIso (congrArg G.obj (Classical.choose_spec h))
  else (hF c h).iso (hG c h)

include hI in
theorem supportedExtensionIsoAt_image (d : D) :
    supportedExtensionIsoAt I F G α hF hG (I.obj d) = α.app d := by
  classical
  have h : I.obj d ∈ Set.range I.obj := ⟨d, rfl⟩
  have hd : Classical.choose h = d := hI (Classical.choose_spec h)
  have aux (d' : D) (h' : I.obj d' = I.obj d) (hd' : d' = d) :
      (eqToIso (congrArg F.obj h')).symm ≪≫ α.app d' ≪≫
        eqToIso (congrArg G.obj h') = α.app d := by
    subst d'
    simp
  simp only [supportedExtensionIsoAt, dif_pos h]
  exact aux _ (Classical.choose_spec h) hd

/-- A comparison on a full injective image extends when both functors vanish elsewhere. -/
def extendSupportedIso [I.Full] : F ≅ G :=
  NatIso.ofComponents (supportedExtensionIsoAt I F G α hF hG) (by
    intro c c' f
    by_cases hc : c ∈ Set.range I.obj
    · obtain ⟨d, rfl⟩ := hc
      by_cases hc' : c' ∈ Set.range I.obj
      · obtain ⟨d', rfl⟩ := hc'
        rw [supportedExtensionIsoAt_image I hI, supportedExtensionIsoAt_image I hI]
        have h := α.hom.naturality (I.preimage f)
        simpa using h
      · exact (hG c' hc').eq_of_tgt _ _
    · exact (hF c hc).eq_of_src _ _)

end MagnitudeConjecture
