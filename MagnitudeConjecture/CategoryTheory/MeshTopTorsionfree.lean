import MagnitudeConjecture.CategoryTheory.MeshProjectiveDetection
import MagnitudeConjecture.CategoryTheory.MeshSimplePresentation
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaInjective

/-!
# Top-torsionfree vertices in a Riedtmann mesh

Condition (b) prevents the simple at a nonprojective vertex from occurring
as a submodule of a contravariant representable.  This is the
top-torsionfree step in the Bongartz--Gabriel injective-resolution argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u

variable {k : Type u} [Field k]
variable {Q : Type} [Quiver.{0} Q]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable (T : RightMeshData Q)

/-- A mesh vertex as an object of the opposite strict vertex category. -/
abbrev oppositeVertexObject (p : Q) :
    (T.VertexCategory (k := k))ᵒᵖ :=
  Opposite.op p

/-- A nonzero map from a mesh simple into `D Hom(p,-)` forces the simple to
be supported at `p`. -/
theorem eq_of_nonzero_map_simple_to_dualCorepresentable
    {z p : Q}
    (hI : IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k
      (dualLinearYonedaLinearModule
        (k := k) (C := (T.VertexCategory (k := k))ᵒᵖ)
        (T.oppositeVertexObject (k := k) p)))
    (f : T.simpleFiniteModule (k := k) z ⟶
      finiteDimensionalDualLinearYoneda
        (k := k) (C := (T.VertexCategory (k := k))ᵒᵖ)
        (T.oppositeVertexObject (k := k) p) hI)
    (hf : f ≠ 0) : z = p := by
  by_contra hzp
  apply hf
  let E := finiteDualLinearYonedaHomEquiv
    (T.simpleFiniteModule (k := k) z)
    (T.oppositeVertexObject (k := k) p) hI
  apply E.injective
  rw [map_zero]
  apply LinearMap.ext
  intro x
  letI : Subsingleton
      ((T.simpleFiniteModule (k := k) z).obj.obj.obj
        (T.oppositeVertexObject (k := k) p)) := by
    change Subsingleton (T.simpleValue (k := k) p z)
    exact T.simpleValue_subsingleton_of_ne (k := k) (Ne.symm hzp)
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  change E f 0 = 0
  exact map_zero _

/-- If a nonzero map sends the mesh simple at `z` into a contravariant
representable, then `z` is projective. -/
theorem mem_projective_of_nonzero_map_simple_to_contravariantRepresentable
    (hP : T.FiniteContravariantRepresentables (k := k))
    (hB : T.RiedtmannConditionB (k := k))
    {z y : Q}
    (f : T.simpleFiniteModule (k := k) z ⟶
      T.contravariantRepresentableFiniteModule (k := k) hP y)
    (hf : f ≠ 0) :
    z ∈ T.projective := by
  by_contra hz
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let fNat := I.map (J.map f)
  have hfz : (fNat.app (Opposite.op z)).hom ≠ 0 := by
    intro hfz
    apply hf
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    rcases X with ⟨X⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    by_cases hX : X = z
    · subst X
      exact DFunLike.congr_fun hfz x
    · letI : Subsingleton
          ((T.simpleFiniteModule (k := k) z).obj.obj.obj
            (Opposite.op X)) := by
        change Subsingleton (T.simpleValue (k := k) X z)
        exact T.simpleValue_subsingleton_of_ne (k := k) hX
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
      change fNat.app (Opposite.op X) 0 = 0
      exact map_zero _
  let e := T.simpleValueSelfLinearEquiv (k := k) z
  let q := fNat.app (Opposite.op z) (e 1)
  have hq : q.hom ≠ 0 := by
    intro hqzero
    apply hfz
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := e.surjective x
    have he : e c = c • e 1 := by
      simpa using (map_smul e c (1 : k))
    calc
      fNat.app (Opposite.op z) (e c) =
          fNat.app (Opposite.op z) (c • e 1) := congrArg _ he
      _ = c • q := (fNat.app (Opposite.op z)).hom.map_smul c (e 1)
      _ = 0 := by
        apply InducedCategory.hom_ext
        change c • q.hom = 0
        rw [hqzero, smul_zero]
  have hBz : T.RiedtmannConditionBAt (k := k) z := by
    simpa only using hB ⟨z, hz⟩
  obtain ⟨a, ha⟩ := hBz y q.hom hq
  let alpha :
      (show T.VertexCategory (k := k) from a.1) ⟶
        (show T.VertexCategory (k := k) from z) :=
    InducedCategory.homMk (T.incomingArrowHom (k := k) a)
  have hsimple :
      ((T.simpleFunctor (k := k) z).map alpha.op) (e 1) = 0 := by
    change Submodule.Quotient.mk
        (T.incomingArrowHom (k := k) a ≫ ((1 : k) • 𝟙 _)) = 0
    rw [one_smul, Category.comp_id, Submodule.Quotient.mk_eq_zero]
    exact mem_lengthTail_of_mem_lengthComponent (k := k) T (by omega)
      (T.incomingArrowHom_mem_lengthComponent_one (k := k) a)
  have hnat := congrArg
    (fun g ↦ g (e 1)) (fNat.naturality alpha.op)
  change
    fNat.app (Opposite.op a.1)
        ((T.simpleFunctor (k := k) z).map alpha.op (e 1)) =
      alpha ≫ q at hnat
  rw [hsimple] at hnat
  have hzero : fNat.app (Opposite.op a.1) 0 = 0 := map_zero _
  have hcompzero : alpha ≫ q = 0 := hnat.symm.trans hzero
  apply ha
  have hraw := congrArg InducedCategory.Hom.hom hcompzero
  have hzeroRaw :
      (0 : (show T.VertexCategory (k := k) from a.1) ⟶
        (show T.VertexCategory (k := k) from y)).hom = 0 :=
    by
      change InducedCategory.homLinearEquiv (R := k) (0 :
        (show T.VertexCategory (k := k) from a.1) ⟶
          (show T.VertexCategory (k := k) from y)) = 0
      exact (InducedCategory.homLinearEquiv (R := k)).map_zero
  exact (by simpa [alpha] using hraw.trans hzeroRaw)

end MagnitudeConjecture.MeshCategory.RightMeshData
