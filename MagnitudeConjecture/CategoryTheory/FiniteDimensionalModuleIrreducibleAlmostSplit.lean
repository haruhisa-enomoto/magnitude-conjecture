import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.AlmostSplitDuality
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteAlmostSplit
import MagnitudeConjecture.CategoryTheory.IrreducibleShortExactAlmostSplit

/-!
# Irreducible short exact sequences in a finite module category

A complete finite indecomposable skeleton supplies a chosen minimal right
almost-split map at every indecomposable endpoint.  Consequently the abstract
irreducible-short-exact comparison theorem can be applied without making the
comparison sequence an extra input.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

namespace FiniteDimensionalModuleIndecomposableSkeleton

variable (V : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))

/-- A short exact complex with two irreducible differentials and an endpoint
in a complete finite indecomposable skeleton is right almost split. -/
theorem isRightAlmostSplit_of_shortExact_of_irreducible
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]
    {S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)}
    (hS : S.ShortExact)
    (hf : IsIrreducibleMorphism S.f)
    (hg : IsIrreducibleMorphism S.g)
    (y : Fin V.n) (e₃ : S.X₃ ≅ V.obj y) :
    IsRightAlmostSplit S.g := by
  have hy : ¬ Projective (V.obj y) := by
    intro hprojective
    letI : Projective (V.obj y) := hprojective
    letI : Projective S.X₃ := Projective.of_iso e₃.symm hprojective
    letI : Epi S.g := hS.epi_g
    apply hg.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := Projective.factorThru (𝟙 S.X₃) S.g
        id := Projective.factorThru_comp (𝟙 S.X₃) S.g }
  let B := V.minimalRightAlmostSplitAt y
  let T : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :=
    ShortComplex.mk (kernel.ι B.map) B.map (kernel.condition B.map)
  have hBepi : Epi B.map :=
    MagnitudeConjecture.CategoryTheory.IsRightAlmostSplit.epi_of_not_projective
      B.map B.rightAlmostSplit hy
  letI : Epi B.map := hBepi
  have hTf : IsLeftAlmostSplit T.f := by
    exact B.rightAlmostSplit.kernel_ι_isLeftAlmostSplit B.map B.rightMinimal
  have hT : T.ShortExact := by
    exact { exact := ShortComplex.exact_kernel B.map }
  have hTleftIndecomposable : Indecomposable T.X₁ := by
    have hop : Indecomposable (Opposite.op T.X₁) :=
      MagnitudeConjecture.CategoryTheory.IsRightAlmostSplit.target_indecomposable
        T.f.op hTf.op
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_op_iff T.X₁).mp hop
  letI : IsLocalRing (End T.X₁) :=
    finiteDimensionalModule_end_isLocalRing k T.X₁ hTleftIndecomposable
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightAlmostSplit_of_irreducible
      hS hT hf hg hTf B.rightAlmostSplit e₃

end FiniteDimensionalModuleIndecomposableSkeleton
end MagnitudeConjecture.CoveringHom
