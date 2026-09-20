import MagnitudeConjecture.Algebra.RightModuleCoordinateEvaluationImage

/-! # Generated-relations quotients inside the literal factor category -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)

/-- The generated-relations quotient of the underlying module of a factor
object, returned to the same literal factor category. -/
def generatedRelationsFactorObj {e : A} (D : PrimitiveIdempotentData e)
    (X : S.FactorCategory (S.primitiveKilledLabels D))
    (R : Submodule k (idempotentCoordinate (k := k) e X.as.obj)) :
    S.FactorCategory (S.primitiveKilledLabels D) :=
  (S.factorModuleFunctor (S.primitiveKilledLabels D)).obj
    (quotientFGObj X.as.obj (generatedCoordinateRelations e X.as.obj R))

/-- The presentation-to-quotient map in the literal factor category. -/
def generatedRelationsFactorMap {e : A} (D : PrimitiveIdempotentData e)
    (X : S.FactorCategory (S.primitiveKilledLabels D))
    (R : Submodule k (idempotentCoordinate (k := k) e X.as.obj)) :
    X ⟶ S.generatedRelationsFactorObj D X R :=
  (S.factorFunctor (S.primitiveKilledLabels D)).map
    (ObjectProperty.homMk (quotientFGMap X.as.obj (generatedCoordinateRelations e X.as.obj R)))

/-- Maps from each factor tau-projective lift through the new quotient,
with all objects and morphisms in the factor category used by realization. -/
theorem generatedRelationsFactorMap_hom_lift
    [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]
    {e : A} (D : PrimitiveIdempotentData e)
    (p : S.FactorProjectiveLabel (S.primitiveKilledLabels D))
    (X : S.FactorCategory (S.primitiveKilledLabels D))
    (R : Submodule k (idempotentCoordinate (k := k) e X.as.obj))
    (f : S.factorObject (S.primitiveKilledLabels D) p.1 ⟶
      S.generatedRelationsFactorObj D X R) :
    ∃ g : S.factorObject (S.primitiveKilledLabels D) p.1 ⟶ X,
      g ≫ S.generatedRelationsFactorMap D X R = f := by
  obtain ⟨f', hf⟩ := (S.factorFunctor (S.primitiveKilledLabels D)).map_surjective f
  obtain ⟨g, hg⟩ := S.generatedRelationsQuotient_hom_lift D p X.as.obj R f'.hom
  let F := S.factorFunctor (S.primitiveKilledLabels D)
  let g' : S.ambientAddPoint p.1.1 ⟶ X.as := ObjectProperty.homMk g
  let q' : X.as ⟶ (S.generatedRelationsFactorObj D X R).as :=
    ObjectProperty.homMk (quotientFGMap X.as.obj (generatedCoordinateRelations e X.as.obj R))
  have hg' : g' ≫ q' = f' := by
    apply ObjectProperty.hom_ext
    exact hg
  refine ⟨F.map g', ?_⟩
  change F.map g' ≫ F.map q' = f
  exact (F.map_comp g' q').symm.trans ((congrArg F.map hg').trans hf)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
