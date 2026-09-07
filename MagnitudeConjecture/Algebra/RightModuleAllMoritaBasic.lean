import MagnitudeConjecture.Algebra.RightModuleBasicMorita
import MagnitudeConjecture.Algebra.RightModuleLeftAlmostSplit
import MagnitudeConjecture.Algebra.RightModuleOppositeProjectivePresentation
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence
import MagnitudeConjecture.CategoryTheory.ModuleGeneratorMorita

/-!
# All-module Morita equivalence to a canonical basic algebra

The finitely generated basic-projective generator already used by the
representation-finite development is also a generator of the category of all
modules. Applying the projective-generator Morita theorem to the
contragredient skeleton gives a Morita equivalence from the original algebra
to the opposite of the contragredient basic endomorphism algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The regular left `A`-module belongs, in the category of all modules, to
the finite additive closure of the basic projective generator selected by the
contragredient skeleton. -/
theorem contragredientBasicProjectiveGenerator_regular_finiteAddClosure :
    MagnitudeConjecture.CategoryTheory.finiteAddClosure
      S.contragredientSkeleton.basicProjectiveGenerator.obj
      (ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ (Aᵐᵒᵖ)ᵐᵒᵖ) := by
  let Sop := S.contragredientSkeleton
  let G := Sop.basicProjectiveGenerator
  let X : FGModuleCat (Aᵐᵒᵖ)ᵐᵒᵖ :=
    FGModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ (Aᵐᵒᵖ)ᵐᵒᵖ
  have hXmodule : Module.Projective (Aᵐᵒᵖ)ᵐᵒᵖ X := inferInstance
  have hX : Projective X :=
    MagnitudeConjecture.fgProjective_of_moduleProjective X hXmodule
  let P :=
    (Sop.finiteAddClosure_basicProjectiveGenerator_of_projective X hX).some
  let U := (ModuleCat.isFG.{u} (Aᵐᵒᵖ)ᵐᵒᵖ).ι
  exact ⟨{
    n := P.n
    retract := (P.retract.map U).trans
      (Retract.ofIso (U.mapBiproduct (fun _ : Fin P.n ↦ G))) }⟩

/-- The all-module Morita equivalence obtained from the contragredient basic
projective generator. The double opposite on the source and the passage from
finitely generated to all-module endomorphisms are both explicit algebra
equivalences. -/
def allModuleMoritaEquivalenceToContragredientBasicOpposite :
    MoritaEquivalence k A
      (S.contragredientSkeleton.moritaBasicAlgebra)ᵐᵒᵖ := by
  let Sop := S.contragredientSkeleton
  let G := Sop.basicProjectiveGenerator
  let U := (ModuleCat.isFG.{u} (Aᵐᵒᵖ)ᵐᵒᵖ).ι
  have hGfg : Projective G := Sop.basicProjectiveGenerator_projective
  letI : Module.Finite (Aᵐᵒᵖ)ᵐᵒᵖ (U.obj G) := G.property
  letI : Module.Projective (Aᵐᵒᵖ)ᵐᵒᵖ (U.obj G) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective G hGfg
  let eEnd : End G ≃ₐ[k] End (U.obj G) :=
    MagnitudeConjecture.CategoryTheory.Functor.endAlgEquivOfFullyFaithful U G
  let eMorita :
      MoritaEquivalence k (Aᵐᵒᵖ)ᵐᵒᵖ (End (U.obj G))ᵐᵒᵖ :=
    MagnitudeConjecture.CategoryTheory.moritaEquivalenceOfProgenerator
      (U.obj G)
      S.contragredientBasicProjectiveGenerator_regular_finiteAddClosure
  exact MoritaEquivalence.trans k
    (MoritaEquivalence.ofAlgEquiv (AlgEquiv.opOp k A)) <|
      MoritaEquivalence.trans k eMorita
        (MoritaEquivalence.ofAlgEquiv (AlgEquiv.op eEnd.symm))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
