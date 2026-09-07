import MagnitudeConjecture.Combinatorics.PosetSpaceBoundaryCover
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Two-term boundary presentations of finite poset spaces

The boundary cover of a poset space is surjective both on its ambient vector
space and on every distinguished subspace.  Its ordinary linear kernel,
equipped with the induced distinguished subspaces, is therefore its kernel in
the category of poset spaces.  Covering that kernel once more gives a
two-term presentation by boundary-projective objects.

This is the target-side exact presentation used in Iyama realization.  It
does not assert that its relation map already has a weak cokernel in the
finite strict tau-category.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

open CategoryTheory CategoryTheory.Limits

universe u

variable {k T : Type u} [Field k] [PartialOrder T]

/-- The kernel of a poset-space morphism, formed on the ambient linear map
and equipped with the induced distinguished subspaces. -/
def kernelObj {X Y : Obj k T} (f : X ⟶ Y) : Obj k T where
  carrier := LinearMap.ker f.linear
  subspace := fun t ↦ (X.subspace t).comap (LinearMap.ker f.linear).subtype
  monotone_subspace := by
    intro s t hst
    exact Submodule.comap_mono (X.monotone_subspace hst)

/-- The canonical inclusion of the induced kernel poset space. -/
def kernelInclusion {X Y : Obj k T} (f : X ⟶ Y) :
    kernelObj f ⟶ X where
  linear := (LinearMap.ker f.linear).subtype
  map_subspace := by
    intro t x hx
    exact hx

@[simp]
theorem kernelInclusion_linear {X Y : Obj k T} (f : X ⟶ Y) :
    (kernelInclusion f).linear = (LinearMap.ker f.linear).subtype :=
  rfl

/-- The kernel inclusion is annihilated by the original morphism. -/
theorem kernelInclusion_comp {X Y : Obj k T} (f : X ⟶ Y) :
    kernelInclusion f ≫ f = 0 := by
  apply Hom.ext
  apply LinearMap.ext
  intro x
  change f.linear x.1 = 0
  exact x.2

/-- A map annihilating `f` factors through the induced kernel object. -/
def kernelLift {W X Y : Obj k T} (f : X ⟶ Y) (g : W ⟶ X)
    (hgf : g ≫ f = 0) : W ⟶ kernelObj f where
  linear := g.linear.codRestrict (LinearMap.ker f.linear) (by
    intro w
    rw [LinearMap.mem_ker]
    have hlinear := congrArg Hom.linear hgf
    have happ := LinearMap.congr_fun hlinear w
    exact happ)
  map_subspace := by
    intro t w hw
    exact g.map_subspace t w hw

@[simp]
theorem kernelLift_comp_inclusion
    {W X Y : Obj k T} (f : X ⟶ Y) (g : W ⟶ X)
    (hgf : g ≫ f = 0) :
    kernelLift f g hgf ≫ kernelInclusion f = g := by
  apply Hom.ext
  apply LinearMap.ext
  intro w
  rfl

namespace BoundarySurjective

/-- A boundary-surjective morphism is the categorical cokernel of its
induced kernel inclusion.  The distinguished-subspace condition is exactly
what makes the linear quotient factor preserve every subspace. -/
def desc {X Y Z : Obj k T} {f : X ⟶ Y}
    (hf : BoundarySurjective f) (q : X ⟶ Z)
    (hq : kernelInclusion f ≫ q = 0) : Y ⟶ Z := by
  have hker : LinearMap.ker f.linear ≤ LinearMap.ker q.linear := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hlinear := congrArg Hom.linear hq
    have happ := LinearMap.congr_fun hlinear ⟨x, hx⟩
    exact happ
  let e := f.linear.quotKerEquivOfSurjective hf.1
  let lift := (LinearMap.ker f.linear).liftQ q.linear hker
  exact
    { linear := lift.comp e.symm.toLinearMap
      map_subspace := by
        intro r y hy
        rw [← hf.2 r] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        change lift (e.symm (f.linear x)) ∈ Z.subspace r
        simpa [e, lift] using q.map_subspace r x hx }

/-- The quotient factor supplied by boundary surjectivity has the requested
composite. -/
theorem comp_desc {X Y Z : Obj k T} {f : X ⟶ Y}
    (hf : BoundarySurjective f) (q : X ⟶ Z)
    (hq : kernelInclusion f ≫ q = 0) :
    f ≫ hf.desc q hq = q := by
  apply Hom.ext
  apply LinearMap.ext
  intro x
  simp [desc]

end BoundarySurjective

section Finite

variable [Fintype T]

/-- The kernel poset space of the canonical boundary cover. -/
abbrev boundaryKernel (Y : Obj k T) : Obj k T :=
  kernelObj (boundaryCoverMap Y)

/-- Covering the kernel supplies the degree-one boundary-projective object. -/
abbrev boundaryRelationObject (Y : Obj k T) : Obj k T :=
  boundaryCover (boundaryKernel Y)

/-- The relation map in the canonical two-term boundary presentation. -/
def boundaryRelationMap (Y : Obj k T) :
    boundaryRelationObject Y ⟶ boundaryCover Y :=
  boundaryCoverMap (boundaryKernel Y) ≫
    kernelInclusion (boundaryCoverMap Y)

/-- The relation map is annihilated by the boundary-cover projection. -/
theorem boundaryRelationMap_comp (Y : Obj k T) :
    boundaryRelationMap Y ≫ boundaryCoverMap Y = 0 := by
  rw [boundaryRelationMap, Category.assoc,
    kernelInclusion_comp, comp_zero]

/-- The canonical boundary-cover projection is a weak cokernel of the
relation map.  Thus every finite poset space has a two-term presentation by
explicit boundary-projective objects. -/
theorem boundaryCoverMap_weakCokernel
    (Y : Obj k T) {Z : Obj k T} (q : boundaryCover Y ⟶ Z)
    (hq : boundaryRelationMap Y ≫ q = 0) :
    ∃ s : Y ⟶ Z, boundaryCoverMap Y ≫ s = q := by
  let c := boundaryCoverMap (boundaryKernel Y)
  haveI : Epi c := boundaryCoverMap_epi (boundaryKernel Y)
  have hkernel : kernelInclusion (boundaryCoverMap Y) ≫ q = 0 := by
    apply (cancel_epi c).1
    simpa only [c, boundaryRelationMap, Category.assoc, comp_zero] using hq
  let hf := boundaryCoverMap_boundarySurjective Y
  exact ⟨hf.desc q hkernel, hf.comp_desc q hkernel⟩

end Finite

end MagnitudeConjecture.PosetSpace
