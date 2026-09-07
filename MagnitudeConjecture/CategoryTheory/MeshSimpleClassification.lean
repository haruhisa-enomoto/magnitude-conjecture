import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.MeshSimplePresentation

/-!
# Classification of simple finite mesh modules

For a finite mesh category with local vertex endomorphism rings, the
categorical radical of each finite representable is its unique maximal
submodule.  Its cokernel is the mesh simple at that vertex, and these exhaust
the simple objects of the finite-dimensional module category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.MeshCategory

universe u

variable {k : Type u} [Field k]
variable {Q : Type} [Quiver.{u} Q]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- The radical cokernel of the representable at a vertex is the explicitly
constructed mesh simple at that vertex. -/
noncomputable def simpleStandardRadicalCokernelIso
    (hP : T.FiniteContravariantRepresentables (k := k))
    (hlocal : ∀ X : (T.VertexCategory (k := k))ᵒᵖ,
      IsLocalRing (End X)) (z : Q) :
    cokernel
        (finiteDimensionalLinearCoyonedaRadicalInclusion
          (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k)
          (show (T.VertexCategory (k := k))ᵒᵖ from Opposite.op z)
          (hP (Opposite.op z))) ≅
      T.simpleFiniteModule (k := k) z := by
  let X : (T.VertexCategory (k := k))ᵒᵖ := Opposite.op z
  let P := finiteDimensionalLinearCoyoneda
    (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k) X (hP X)
  let r := finiteDimensionalLinearCoyonedaRadicalInclusion
    (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k) X (hP X)
  let q := T.simpleStandardAugmentation (k := k) hP z
  letI : Projective P :=
    finiteDimensionalLinearCoyoneda_projective X (hP X)
  letI : IsLocalRing (End P) :=
    finiteDimensionalLinearCoyoneda_end_isLocalRing hP hlocal X
  have hr : IsRightAlmostSplit r :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP hlocal X
  have hq : q ≠ 0 := by
    intro hzero
    apply CategoryTheory.id_nonzero (T.simpleFiniteModule (k := k) z)
    apply (cancel_epi q).1
    rw [Category.comp_id, hzero, zero_comp]
  exact
    MagnitudeConjecture.CategoryTheory.cokernelIsoSimpleTarget_of_mono_rightAlmostSplit_projective
      r hr q hq

/-- Every simple finite-dimensional module on a finite mesh category is the
mesh simple supported at one of its vertices. -/
theorem exists_iso_simpleFiniteModule_of_simple
    (hP : T.FiniteContravariantRepresentables (k := k))
    (hlocal : ∀ X : (T.VertexCategory (k := k))ᵒᵖ,
      IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) [Simple M] :
    ∃ z : Q, Nonempty (M ≅ T.simpleFiniteModule (k := k) z) := by
  classical
  have hex : ∃ (z : Q) (x : M.obj.obj.obj (Opposite.op z)), x ≠ 0 := by
    by_contra h
    push Not at h
    apply CategoryTheory.id_nonzero M
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    rcases X with ⟨z⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = 0
    exact h z x
  obtain ⟨z, x, hx⟩ := hex
  let X : (T.VertexCategory (k := k))ᵒᵖ := Opposite.op z
  let P := finiteDimensionalLinearCoyoneda
    (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k) X (hP X)
  let r := finiteDimensionalLinearCoyonedaRadicalInclusion
    (C := (T.VertexCategory (k := k))ᵒᵖ) (k := k) X (hP X)
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let pLinear : J.obj P ⟶ J.obj M :=
    linearCoyonedaHom M.obj X x
  let p : P ⟶ M := J.preimage pLinear
  have hp : p ≠ 0 := by
    intro hzero
    apply hx
    have hmap : J.map p = pLinear := by
      dsimp only [p]
      exact J.map_preimage pLinear
    have hz := congrArg
      (fun f : P ⟶ M ↦ (J.map f).hom.app X (𝟙 X)) hzero
    rw [hmap, J.map_zero] at hz
    change (linearCoyonedaHom M.obj X x).hom.app X (𝟙 X) = 0 at hz
    rw [linearCoyonedaHom_app_id] at hz
    exact hz
  letI : Projective P :=
    finiteDimensionalLinearCoyoneda_projective X (hP X)
  letI : IsLocalRing (End P) :=
    finiteDimensionalLinearCoyoneda_end_isLocalRing hP hlocal X
  have hr : IsRightAlmostSplit r :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP hlocal X
  let eM : cokernel r ≅ M :=
    MagnitudeConjecture.CategoryTheory.cokernelIsoSimpleTarget_of_mono_rightAlmostSplit_projective
      r hr p hp
  let eS : cokernel r ≅ T.simpleFiniteModule (k := k) z :=
    T.simpleStandardRadicalCokernelIso (k := k) hP hlocal z
  exact ⟨z, ⟨eM.symm ≪≫ eS⟩⟩

end RightMeshData

end MagnitudeConjecture.MeshCategory
