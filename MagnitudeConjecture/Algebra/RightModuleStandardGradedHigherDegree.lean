import MagnitudeConjecture.Algebra.RightModuleStandardGradedDegreeOne
import MagnitudeConjecture.CategoryTheory.PathDegreeFactorization
import MagnitudeConjecture.CategoryTheory.NoBackwardFactorization

/-! # Higher-degree graded maps factor with neither factor split -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance rdGradedHigherDegreeQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance rdGradedHigherDegreeArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

set_option maxHeartbeats 1200000 in
/-- Every map of degree n+1, n positive, factors through intermediate shifted
modules admitting no reverse maps to either endpoint. -/
theorem standardFormGraded_higherDegree_factorization
    (X Y : S.StandardFormMeshCategory) (t : ℤ) (n : ℕ) (hn : 0 < n)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, t + n + 1⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩) :
    f ∈ MagnitudeConjecture.CategoryTheory.noBackwardFactorizations (k := k) _ _ := by
  let F := S.standardFormGradedVertexFunctor
  let H := Graded.FiniteGradedModule.homGrading
    (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
  let U : Graded.FiniteGradedModule.ShiftedModule := ⟨F.obj X, t + n + 1⟩
  let V : Graded.FiniteGradedModule.ShiftedModule := ⟨F.obj Y, t⟩
  let B := MagnitudeConjecture.CategoryTheory.noBackwardFactorizations (k := k) U V
  let L := (H.component (F.obj X) (F.obj Y) ((t + n + 1) - t)).subtype
  let P : Submodule k (X ⟶ Y) := (B.map L).comap (F.mapLinearMap k)
  have hspan : Submodule.span k
      (LinearPathCategory.HomogeneousQuotient.firstDegreeComposites
        (S.standardFormRightMeshData.meshGeneratorSet (k := k)) X.as Y.as n) ≤ P := by
    apply Submodule.span_le.mpr
    rintro q ⟨z, a, b, ha, hb, rfl⟩
    let Z := MeshCategory.obj (k := k) S.standardFormRightMeshData z
    let W : Graded.FiniteGradedModule.ShiftedModule := ⟨F.obj Z, t + n⟩
    have ha0 : a ∈ S.standardFormIntegerHomGrading.component X Z 1 := by
      change a ∈ Graded.integerComponent (MeshCategory.lengthComponent S.standardFormRightMeshData X.as z) 1
      simpa [Graded.integerComponent, MeshCategory.lengthComponent] using ha
    have hb0 : b ∈ S.standardFormIntegerHomGrading.component Z Y (n : ℤ) := by
      change b ∈ Graded.integerComponent (MeshCategory.lengthComponent S.standardFormRightMeshData z Y.as) (n : ℤ)
      simpa only [Graded.integerComponent_nat, MeshCategory.lengthComponent] using hb
    let a' : U ⟶ W := ⟨F.map a, by
      change F.map a ∈ H.component (F.obj X) (F.obj Z) ((t + n + 1) - (t + n))
      rw [show (t + n + 1) - (t + n) = 1 by omega]
      exact S.standardFormGradedVertexFunctor_homogeneous ha0⟩
    let b' : W ⟶ V := ⟨F.map b, by
      change F.map b ∈ H.component (F.obj Z) (F.obj Y) ((t + n) - t)
      rw [show (t + n) - t = (n : ℤ) by omega]
      exact S.standardFormGradedVertexFunctor_homogeneous hb0⟩
    change F.map (a ≫ b) ∈ B.map L
    refine ⟨a' ≫ b', ?_, ?_⟩
    · refine ⟨W, a', b', rfl, ?_, ?_⟩
      · intro r
        by_contra hr
        have hd := S.standardFormGraded_strict_descent Z X (t + n) (t + n + 1) r hr
          (Or.inr (by omega))
        omega
      · intro r
        by_contra hr
        have hd := S.standardFormGraded_strict_descent Y Z t (t + n) r hr
          (Or.inr (by omega))
        omega
    · exact (F.map_comp a b).symm
  let e := S.standardFormGradedHomEquiv X Y (t + n + 1) t
  let g := e.symm f
  have hg : g.val ∈ MeshCategory.lengthComponent S.standardFormRightMeshData X.as Y.as (n + 1) := by
    have hh := g.property
    change g.val ∈ Graded.integerComponent
      (MeshCategory.lengthComponent S.standardFormRightMeshData X.as Y.as) ((t + n + 1) - t) at hh
    simpa only [show (t + n + 1) - t = ((n + 1 : ℕ) : ℤ) by omega,
      Graded.integerComponent_nat] using hh
  have hp : g.val ∈ P := hspan
    (LinearPathCategory.HomogeneousQuotient.lengthComponent_le_firstDegreeComposites
      (S.standardFormRightMeshData.meshGeneratorSet (k := k)) X.as Y.as n hg)
  obtain ⟨q, hq, heq⟩ := hp
  have he : F.map g.val = f.val := congrArg Subtype.val (e.apply_symm_apply f)
  have hqf : q = f := Subtype.ext (heq.trans he)
  exact hqf ▸ hq

/-- Nonzero higher-degree maps are not irreducible. -/
theorem standardFormGraded_higherDegree_not_irreducible
    (X Y : S.StandardFormMeshCategory) (t : ℤ) (n : ℕ) (hn : 0 < n)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, t + n + 1⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩) (hf : f ≠ 0) : ¬ IsIrreducibleMorphism f :=
  MagnitudeConjecture.CategoryTheory.not_irreducible_of_noBackwardFactorization hf
    (S.standardFormGraded_higherDegree_factorization X Y t n hn f)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
