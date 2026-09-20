import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleLocalRepresentationFinite

/-! # Indecomposable modules are supported on one orthogonal block -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
universe u v w
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {J : Type w} (block : C → J)
variable (hcross : ∀ X Y : C, block X ≠ block Y → ∀ f : X ⟶ Y, f = 0)
variable (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)

/-- The natural projection of a module onto one orthogonal block. -/
def orthogonalBlockProjection (j : J) : End M := by
  classical
  refine ObjectProperty.homMk (ObjectProperty.homMk
    { app := fun X ↦ if block X = j then 𝟙 _ else 0
      naturality := ?_ })
  intro X Y f
  by_cases hx : block X = j <;> by_cases hy : block Y = j
  · simp [hx, hy]
  · have hf : f = 0 := hcross X Y (fun h ↦ hy (h.symm.trans hx)) f
    simp [hx, hy, hf]
  · have hf : f = 0 := hcross X Y (fun h ↦ hx (h.trans hy)) f
    simp [hx, hy, hf]
  · simp [hx, hy]

/-- A block projection is an idempotent endomorphism. -/
theorem orthogonalBlockProjection_idempotent (j : J) :
    IsIdempotentElem (orthogonalBlockProjection block hcross M j) := by
  classical
  change orthogonalBlockProjection block hcross M j ≫
    orthogonalBlockProjection block hcross M j = orthogonalBlockProjection block hcross M j
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  change (if block X = j then 𝟙 _ else 0) ≫ (if block X = j then 𝟙 _ else 0) =
    (if block X = j then 𝟙 _ else 0)
  split_ifs <;> simp

/-- An indecomposable finite module is nonzero at some base object. -/
theorem exists_nonzero_fiber_of_indecomposable (hM : Indecomposable M) :
    ∃ X : C, ¬ IsZero (M.obj.obj.obj X) := by
  by_contra h
  push_neg at h
  have hfunctor : IsZero M.obj.obj := Functor.isZero M.obj.obj h
  have hlinear : IsZero M.obj :=
    IsZero.of_full_of_faithful_of_isZero (IsLinearModule (C := C) k).ι M.obj hfunctor
  exact hM.1 (IsZero.of_full_of_faithful_of_isZero
    (IsFiniteDimensionalModule (C := C) k).ι M hlinear)

/-- A projection containing a nonzero fiber of an indecomposable is the identity. -/
theorem orthogonalBlockProjection_eq_id (hM : Indecomposable M) (X : C)
    (hX : ¬ IsZero (M.obj.obj.obj X)) :
    orthogonalBlockProjection block hcross M (block X) = 𝟙 M := by
  classical
  let := finiteDimensionalModule_end_isLocalRing k M hM
  rcases QuotientSubmoduleEquidistribution.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
    (orthogonalBlockProjection_idempotent block hcross M (block X)) with hz | hi
  · exfalso
    apply hX
    apply (IsZero.iff_id_eq_zero _).mpr
    have he := congrArg (fun f : End M ↦ f.hom.hom.app X) hz
    simpa [orthogonalBlockProjection] using he
  · exact hi

include hcross

/-- A module indecomposable has zero fibers outside the block of any nonzero fiber. -/
theorem isZero_fiber_of_block_ne (hM : Indecomposable M) (X : C)
    (hX : ¬ IsZero (M.obj.obj.obj X)) (Y : C) (hYX : block Y ≠ block X) :
    IsZero (M.obj.obj.obj Y) := by
  classical
  have he := congrArg (fun f : End M ↦ f.hom.hom.app Y)
    (orthogonalBlockProjection_eq_id block hcross M hM X hX)
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa [orthogonalBlockProjection, hYX] using he.symm

/-- Exactly one orthogonal block supports an indecomposable finite module. -/
theorem existsUnique_support_block (hM : Indecomposable M) :
    ∃! j : J, ∀ X : C, block X ≠ j → IsZero (M.obj.obj.obj X) := by
  obtain ⟨X, hX⟩ := exists_nonzero_fiber_of_indecomposable M hM
  refine ⟨block X, fun Y hY ↦ isZero_fiber_of_block_ne block hcross M hM X hX Y hY, ?_⟩
  intro j hj
  by_contra hne
  exact hX (hj X (Ne.symm hne))

omit hcross in
/-- A nonzero module map is nonzero at some object, where both fibers are nonzero. -/
theorem nonzero_map_has_nonzero_fibers
    (N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (f : N ⟶ M) (hf : f ≠ 0) :
    ∃ X : C, ¬ IsZero (N.obj.obj.obj X) ∧ ¬ IsZero (M.obj.obj.obj X) := by
  have hex : ∃ X : C, f.hom.hom.app X ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact h X
  obtain ⟨X, hX⟩ := hex
  exact ⟨X, fun hz ↦ hX (hz.eq_of_src _ _), fun hz ↦ hX (hz.eq_of_tgt _ _)⟩

/-- Every indecomposable mapping nontrivially into a block-supported module
is supported on that same block. -/
theorem incoming_source_supported_on_block (j : J)
    (hM : ∀ X : C, block X ≠ j → IsZero (M.obj.obj.obj X))
    (N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hN : Indecomposable N) (f : N ⟶ M) (hf : f ≠ 0) :
    ∀ Y : C, block Y ≠ j → IsZero (N.obj.obj.obj Y) := by
  obtain ⟨X, hNX, hMX⟩ := nonzero_map_has_nonzero_fibers M N f hf
  have hX : block X = j := by
    by_contra h
    exact hMX (hM X h)
  intro Y hY
  exact isZero_fiber_of_block_ne block hcross N hN X hNX Y (by simpa [hX] using hY)

end MagnitudeConjecture.CoveringHom
