import MagnitudeConjecture.Algebra.RightModuleSimpleTop
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Counting simple modules by indecomposable projectives

Taking the simple top gives a bijection between the projective labels and
the simple labels of a complete finite indecomposable right-module family.
Consequently, the projective count used by the magnitude calculation equals
the literal number of simple-module isomorphism classes.

The bijection works over any field. Algebraic closedness is unnecessary.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Labels whose representatives are simple right modules. Completeness and
absence of repeated isomorphism classes make their cardinality the simple count. -/
abbrev SimpleLabel := {i : Fin S.n // IsSimpleModule Aᵐᵒᵖ (S.fgObj i)}

/-- The literal number of simple-module classes in the family. -/
def simpleCount : ℕ := Nat.card S.SimpleLabel

/-- The simple top of each projective occurs in the complete family. -/
theorem exists_simpleLabel_top_iso (p : S.ProjectiveLabel) :
    ∃ i : S.SimpleLabel, Nonempty (S.projectiveSimpleTop p ≅ S.fgObj i.1) := by
  let : IsSimpleModule Aᵐᵒᵖ (S.projectiveSimpleTop p) :=
    S.projectiveSimpleTop_isSimpleModule p
  let : Simple (S.projectiveSimpleTop p) :=
    fgModule_simple_of_isSimpleModule _
  obtain ⟨i, ⟨e⟩⟩ := S.fgObj_complete (S.projectiveSimpleTop p)
    (indecomposable_of_simple (S.projectiveSimpleTop p))
  let : Simple (S.fgObj i) := Simple.of_iso e.symm
  exact ⟨⟨i, fgModule_isSimpleModule_of_simple _⟩, ⟨e⟩⟩

/-- The label of the simple top of a projective representative. -/
def simpleTopLabel (p : S.ProjectiveLabel) : S.SimpleLabel :=
  (S.exists_simpleLabel_top_iso p).choose

/-- The chosen identification of a projective's top with its simple representative. -/
def simpleTopLabelIso (p : S.ProjectiveLabel) :
    S.projectiveSimpleTop p ≅ S.fgObj (S.simpleTopLabel p).1 :=
  (S.exists_simpleLabel_top_iso p).choose_spec.some

/-- Distinct indecomposable projectives have nonisomorphic simple tops. -/
theorem simpleTopLabel_injective : Function.Injective S.simpleTopLabel := by
  intro p q hpq
  by_contra hne
  let e : S.projectiveSimpleTop p ≅ S.projectiveSimpleTop q :=
    (S.simpleTopLabelIso p).trans
      ((eqToIso (congrArg (fun i : S.SimpleLabel ↦ S.fgObj i.1) hpq)).trans
        (S.simpleTopLabelIso q).symm)
  have hzero := S.hom_projectiveSimpleTop_eq_zero q p hne
    (S.projectiveSimpleTopProjection p ≫ e.hom)
  apply S.projectiveSimpleTopProjection_ne_zero p
  apply (cancel_mono e.hom).1
  simpa using hzero

/-- A map from a projective to a simple module descends to its simple top. -/
def simpleTopDesc (p : S.ProjectiveLabel) (i : S.SimpleLabel)
    (f : S.fgObj p.label ⟶ S.fgObj i.1) :
    S.projectiveSimpleTop p ⟶ S.fgObj i.1 := by
  let : IsSimpleModule Aᵐᵒᵖ (S.fgObj i.1) := i.2
  exact ⟨ModuleCat.ofHom
    ((Module.jacobson Aᵐᵒᵖ (S.fgObj p.label)).liftQ f.hom.hom
      (IsSemisimpleModule.jacobson_le_ker Aᵐᵒᵖ Aᵐᵒᵖ
        (S.fgObj p.label) (S.fgObj i.1) f.hom.hom))⟩

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- Descent recovers the original map after the top projection. -/
@[simp] theorem projectiveSimpleTopProjection_desc
    (p : S.ProjectiveLabel) (i : S.SimpleLabel)
    (f : S.fgObj p.label ⟶ S.fgObj i.1) :
    S.projectiveSimpleTopProjection p ≫ S.simpleTopDesc p i f = f := by
  apply FGModuleCat.hom_ext
  ext x
  rfl

/-- Every simple representative is the top of an indecomposable projective. -/
theorem simpleTopLabel_surjective : Function.Surjective S.simpleTopLabel := by
  intro i
  obtain ⟨p, f, hf⟩ := S.exists_projectiveLabel_hom_ne_zero i.1
  let : IsSimpleModule Aᵐᵒᵖ (S.fgObj i.1) := i.2
  let : Simple (S.fgObj i.1) := fgModule_simple_of_isSimpleModule _
  let : IsSimpleModule Aᵐᵒᵖ (S.projectiveSimpleTop p) :=
    S.projectiveSimpleTop_isSimpleModule p
  let : Simple (S.projectiveSimpleTop p) := fgModule_simple_of_isSimpleModule _
  have hdesc : S.simpleTopDesc p i f ≠ 0 := by
    intro hzero
    apply hf
    rw [← S.projectiveSimpleTopProjection_desc p i f, hzero, comp_zero]
  let : IsIso (S.simpleTopDesc p i f) := (isIso_iff_nonzero _).2 hdesc
  refine ⟨p, Subtype.ext (S.fgObj_skeletal ?_)⟩
  exact ⟨(S.simpleTopLabelIso p).symm.trans (asIso (S.simpleTopDesc p i f))⟩

/-- Taking the top identifies projective classes with simple classes. -/
def projectiveLabelEquivSimpleLabel : S.ProjectiveLabel ≃ S.SimpleLabel :=
  Equiv.ofBijective S.simpleTopLabel
    ⟨S.simpleTopLabel_injective, S.simpleTopLabel_surjective⟩

/-- The simple count equals the number of indecomposable projectives. -/
theorem simpleCount_eq_card_projectiveLabel :
    S.simpleCount = Fintype.card S.ProjectiveLabel := by
  rw [simpleCount, ← Nat.card_congr S.projectiveLabelEquivSimpleLabel,
    Nat.card_eq_fintype_card]

/-- The literal simple count is the integer projective count used in the
magnitude formula. -/
theorem simpleCount_eq_projectiveCount :
    (S.simpleCount : ℤ) =
      @ARCount.projectiveCount (Fin S.n) inferInstance
        (fun i ↦ Projective (S.fgObj i)) (Classical.decPred _) := by
  classical
  rw [S.simpleCount_eq_card_projectiveLabel, ARCount.projectiveCount,
    Fintype.card_congr S.projectiveLabelEquivSubtype]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
