import MagnitudeConjecture.Combinatorics.PosetSpaceBoundary
import MagnitudeConjecture.Combinatorics.PosetSpaceRealization
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Poset spaces as injective diagrams on the augmented boundary

The augmented boundary is a root adjoined below `OrderDual T`.  A `T`-space
gives a contravariant diagram on this boundary: its value at the root is the
ambient vector space, its value at `t` is the distinguished subspace at `t`,
and every structure map into the root is the subtype inclusion.

This file proves the converse.  A finite-dimensional boundary diagram whose
maps into the root are injective is recovered by taking their ranges in the
root.  Thus finite `T`-spaces are equivalent to precisely these diagrams.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

open CategoryTheory
open Opposite

universe u

variable (k T : Type u) [Field k] [PartialOrder T]

/-- The module attached by a `T`-space to a boundary index. -/
def boundarySpace (Y : Obj k T) : BoundaryIndex T → ModuleCat.{u} k
  | .root => ModuleCat.of k Y
  | .nonroot t => ModuleCat.of k (Y.subspace t)

/-- The contravariant restriction map attached to an inequality in the
augmented boundary. -/
def boundaryRestriction (Y : Obj k T) {q r : BoundaryIndex T} (h : q ≤ r) :
    boundarySpace k T Y r ⟶ boundarySpace k T Y q := by
  cases q with
  | root =>
      cases r with
      | root => exact ModuleCat.ofHom LinearMap.id
      | nonroot t => exact ModuleCat.ofHom (Y.subspace t).subtype
  | nonroot t =>
      cases r with
      | root => exact False.elim h
      | nonroot s =>
          exact ModuleCat.ofHom (Submodule.inclusion (Y.monotone_subspace h))

@[simp]
theorem boundaryRestriction_root_root (Y : Obj k T)
    (h : (BoundaryIndex.root : BoundaryIndex T) ≤ .root) :
    boundaryRestriction k T Y h = 𝟙 _ :=
  rfl

@[simp]
theorem boundaryRestriction_root_nonroot (Y : Obj k T) (t : T)
    (h : (BoundaryIndex.root : BoundaryIndex T) ≤ .nonroot t) :
    (boundaryRestriction k T Y h).hom = (Y.subspace t).subtype :=
  rfl

@[simp]
theorem boundaryRestriction_nonroot_nonroot (Y : Obj k T) (s t : T)
    (h : (BoundaryIndex.nonroot t : BoundaryIndex T) ≤ .nonroot s) :
    (boundaryRestriction k T Y h).hom =
      Submodule.inclusion (Y.monotone_subspace h) :=
  rfl

theorem boundaryRestriction_refl (Y : Obj k T) (q : BoundaryIndex T) :
    boundaryRestriction k T Y (le_refl q) = 𝟙 _ := by
  cases q with
  | root => rfl
  | nonroot t =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl

theorem boundaryRestriction_trans (Y : Obj k T)
    {q r s : BoundaryIndex T} (hqr : q ≤ r) (hrs : r ≤ s) :
    boundaryRestriction k T Y (hqr.trans hrs) =
      boundaryRestriction k T Y hrs ≫ boundaryRestriction k T Y hqr := by
  cases q with
  | root =>
      cases r with
      | root =>
          cases s <;> apply ModuleCat.hom_ext <;>
            apply LinearMap.ext <;> intro x <;> rfl
      | nonroot t =>
          cases s with
          | root => exact False.elim hrs
          | nonroot v =>
              apply ModuleCat.hom_ext
              apply LinearMap.ext
              intro x
              rfl
  | nonroot t =>
      cases r with
      | root => exact False.elim hqr
      | nonroot v =>
          cases s with
          | root => exact False.elim hrs
          | nonroot w =>
              apply ModuleCat.hom_ext
              apply LinearMap.ext
              intro x
              rfl

/-- The contravariant boundary diagram of a `T`-space. -/
def boundaryDiagram (Y : Obj k T) :
    (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj q := boundarySpace k T Y q.unop
  map f := boundaryRestriction k T Y (le_of_op_hom f)
  map_id q := by
    exact boundaryRestriction_refl k T Y q.unop
  map_comp f g := by
    exact boundaryRestriction_trans k T Y
      (le_of_op_hom g) (le_of_op_hom f)

@[simp]
theorem boundaryDiagram_obj_root (Y : Obj k T) :
    (boundaryDiagram k T Y).obj (op (.root : BoundaryIndex T)) =
      ModuleCat.of k Y :=
  rfl

@[simp]
theorem boundaryDiagram_obj_nonroot (Y : Obj k T) (t : T) :
    (boundaryDiagram k T Y).obj (op (.nonroot t : BoundaryIndex T)) =
      ModuleCat.of k (Y.subspace t) :=
  rfl

/-- The canonical arrow from a non-root boundary point to the root in the
opposite boundary category. -/
def boundaryRootArrow (t : T) :
    op (BoundaryIndex.nonroot t) ⟶ op (BoundaryIndex.root : BoundaryIndex T) :=
  (homOfLE (show (BoundaryIndex.root : BoundaryIndex T) ≤ .nonroot t by
    trivial)).op

/-- If `s ≤ t` in `T`, contravariance gives an arrow from the value at `s`
to the value at `t`. -/
def boundaryNonrootArrow {s t : T} (hst : s ≤ t) :
    op (BoundaryIndex.nonroot s) ⟶ op (BoundaryIndex.nonroot t) :=
  (homOfLE
    (show (BoundaryIndex.nonroot t : BoundaryIndex T) ≤ .nonroot s from hst)).op

@[simp]
theorem boundaryDiagram_map_rootArrow_hom (Y : Obj k T) (t : T) :
    ((boundaryDiagram k T Y).map (boundaryRootArrow T t)).hom =
      (Y.subspace t).subtype :=
  rfl

/-- The component of a morphism of `T`-spaces on its boundary diagram. -/
def boundaryDiagramMap {X Y : Obj k T} (f : X ⟶ Y) :
    boundaryDiagram k T X ⟶ boundaryDiagram k T Y where
  app q := by
    cases q using Opposite.rec with
    | _ q =>
        cases q with
        | root => exact ModuleCat.ofHom f.linear
        | nonroot t =>
            exact ModuleCat.ofHom
              (LinearMap.restrict (p := X.subspace t) (q := Y.subspace t)
                f.linear (f.map_subspace t))
  naturality a b g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases a using Opposite.rec with
    | _ a =>
        cases b using Opposite.rec with
        | _ b =>
            have hba : b ≤ a := le_of_op_hom g
            cases b with
            | root =>
                cases a with
                | root => rfl
                | nonroot t => rfl
            | nonroot t =>
                cases a with
                | root => exact False.elim hba
                | nonroot s => rfl

@[simp]
theorem boundaryDiagramMap_app_root_linear {X Y : Obj k T} (f : X ⟶ Y) :
    ((boundaryDiagramMap k T f).app (op (.root : BoundaryIndex T))).hom =
      f.linear :=
  rfl

/-- Sending a poset space to its boundary diagram is functorial. -/
def boundaryDiagramFunctor :
    Obj k T ⥤ ((BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) where
  obj := boundaryDiagram k T
  map := boundaryDiagramMap k T
  map_id X := by
    ext q x
    cases q using Opposite.rec with
    | _ q =>
        cases q with
        | root => rfl
        | nonroot t => apply Subtype.ext; rfl
  map_comp f g := by
    ext q x
    cases q using Opposite.rec with
    | _ q =>
        cases q with
        | root => rfl
        | nonroot t => apply Subtype.ext; rfl

/-- A boundary diagram has the form required by a finite poset space when all
its values are finite-dimensional and every structure map from a non-root
value into the root is injective. -/
def IsFiniteInjectiveBoundaryDiagram :
    ObjectProperty ((BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :=
  fun F ↦
    (∀ q : BoundaryIndex T, Module.Finite k (F.obj (op q))) ∧
      ∀ t : T, Function.Injective
        ((F.map (boundaryRootArrow T t)).hom)

/-- The full category of finite-dimensional boundary diagrams with injective
maps into the root. -/
abbrev FiniteInjectiveBoundaryDiagram :=
  (IsFiniteInjectiveBoundaryDiagram k T).FullSubcategory

theorem boundaryDiagram_isFiniteInjective (Y : Obj k T) :
    IsFiniteInjectiveBoundaryDiagram k T (boundaryDiagram k T Y) := by
  constructor
  · intro q
    cases q with
    | root =>
        change Module.Finite k Y
        exact Y.finiteDimensional
    | nonroot t =>
        change Module.Finite k (Y.subspace t)
        infer_instance
  · intro t
    exact (Y.subspace t).injective_subtype

/-- The boundary-diagram functor with its codomain restricted to the exact
finite injective image condition. -/
def finiteInjectiveBoundaryDiagramFunctor :
    Obj k T ⥤ FiniteInjectiveBoundaryDiagram k T :=
  (IsFiniteInjectiveBoundaryDiagram k T).lift
    (boundaryDiagramFunctor k T) (boundaryDiagram_isFiniteInjective k T)

/-- The root component of a natural transformation of boundary diagrams. -/
def boundaryDiagramMapRoot {X Y : Obj k T}
    (α : boundaryDiagram k T X ⟶ boundaryDiagram k T Y) : X →ₗ[k] Y := by
  exact (α.app (op (.root : BoundaryIndex T))).hom

/-- A non-root component of a natural transformation of boundary diagrams. -/
def boundaryDiagramMapNonroot {X Y : Obj k T}
    (α : boundaryDiagram k T X ⟶ boundaryDiagram k T Y) (t : T) :
    X.subspace t →ₗ[k] Y.subspace t := by
  exact (α.app (op (.nonroot t : BoundaryIndex T))).hom

/-- Naturality at the arrow into the root says that the root component
restricts to each non-root component. -/
theorem boundaryDiagramMap_root_eq_nonroot {X Y : Obj k T}
    (α : boundaryDiagram k T X ⟶ boundaryDiagram k T Y) (t : T)
    (x : X.subspace t) :
    boundaryDiagramMapRoot k T α x =
      (boundaryDiagramMapNonroot k T α t x : Y) := by
  have hnat := α.naturality (boundaryRootArrow T t)
  have happ := congrArg (fun f ↦ f.hom x) hnat
  change boundaryDiagramMapRoot k T α x =
    (boundaryDiagramMapNonroot k T α t x : Y) at happ
  exact happ

/-- A natural transformation between boundary diagrams is determined at the
root and therefore induces a morphism of the underlying poset spaces. -/
def homOfBoundaryDiagramMap {X Y : Obj k T}
    (α : boundaryDiagram k T X ⟶ boundaryDiagram k T Y) : X ⟶ Y where
  linear := boundaryDiagramMapRoot k T α
  map_subspace := by
    intro t x hx
    let xt : X.subspace t := ⟨x, hx⟩
    rw [boundaryDiagramMap_root_eq_nonroot k T α t xt]
    exact (boundaryDiagramMapNonroot k T α t xt).property

theorem boundaryDiagramMap_homOfBoundaryDiagramMap {X Y : Obj k T}
    (α : boundaryDiagram k T X ⟶ boundaryDiagram k T Y) :
    boundaryDiagramMap k T (homOfBoundaryDiagramMap k T α) = α := by
  ext q x
  cases q using Opposite.rec with
  | _ q =>
      cases q with
      | root => rfl
      | nonroot t =>
          apply Subtype.ext
          exact boundaryDiagramMap_root_eq_nonroot k T α t x

instance finiteInjectiveBoundaryDiagramFunctor_faithful :
    (finiteInjectiveBoundaryDiagramFunctor k T).Faithful where
  map_injective := by
    intro X Y f g h
    apply Hom.ext
    have happ := congrArg
      (fun a ↦ (a.hom.app (op (.root : BoundaryIndex T))).hom) h
    exact happ

instance finiteInjectiveBoundaryDiagramFunctor_full :
    (finiteInjectiveBoundaryDiagramFunctor k T).Full where
  map_surjective := by
    intro X Y α
    let f := homOfBoundaryDiagramMap k T α.hom
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    exact boundaryDiagramMap_homOfBoundaryDiagramMap k T α.hom

/-- The structure map of an arbitrary boundary diagram into its root. -/
def boundaryDiagramRootMap
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) (t : T) :
    F.obj (op (.nonroot t : BoundaryIndex T)) →ₗ[k]
      F.obj (op (.root : BoundaryIndex T)) :=
  (F.map (boundaryRootArrow T t)).hom

/-- The map along a comparable pair of non-root points commutes with the two
maps into the root. -/
theorem boundaryDiagramRootMap_map_nonroot
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k)
    {s t : T} (hst : s ≤ t)
    (y : F.obj (op (.nonroot s : BoundaryIndex T))) :
    boundaryDiagramRootMap k T F t
        ((F.map (boundaryNonrootArrow T hst)).hom y) =
      boundaryDiagramRootMap k T F s y := by
  have harrow :
      boundaryNonrootArrow T hst ≫ boundaryRootArrow T t =
        boundaryRootArrow T s :=
    Subsingleton.elim _ _
  calc
    boundaryDiagramRootMap k T F t
        ((F.map (boundaryNonrootArrow T hst)).hom y) =
        ((F.map (boundaryNonrootArrow T hst) ≫
          F.map (boundaryRootArrow T t)).hom y) := rfl
    _ = (F.map
        (boundaryNonrootArrow T hst ≫ boundaryRootArrow T t)).hom y := by
          rw [F.map_comp]
    _ = boundaryDiagramRootMap k T F s y := by
      rw [harrow]
      rfl

/-- Reconstruct a poset space from a finite injective boundary diagram by
taking the ranges of all structure maps inside the root value. -/
def posetSpaceOfBoundaryDiagram (F : FiniteInjectiveBoundaryDiagram k T) :
    Obj k T where
  carrier := F.obj.obj (op (.root : BoundaryIndex T))
  finiteDimensional := F.property.1 .root
  subspace t := LinearMap.range (boundaryDiagramRootMap k T F.obj t)
  monotone_subspace := by
    intro s t hst x hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(F.obj.map (boundaryNonrootArrow T hst)).hom y, ?_⟩
    exact boundaryDiagramRootMap_map_nonroot k T F.obj hst y

/-- An injective root map identifies a non-root value with its range in the
root. -/
def boundaryRangeLinearEquiv (F : FiniteInjectiveBoundaryDiagram k T)
    (t : T) :
    F.obj.obj (op (.nonroot t : BoundaryIndex T)) ≃ₗ[k]
      LinearMap.range (boundaryDiagramRootMap k T F.obj t) :=
  LinearEquiv.ofBijective
    (boundaryDiagramRootMap k T F.obj t).rangeRestrict
    ⟨(LinearMap.injective_rangeRestrict_iff
        (boundaryDiagramRootMap k T F.obj t)).2 (F.property.2 t),
      (boundaryDiagramRootMap k T F.obj t).surjective_rangeRestrict⟩

/-- Componentwise identification of the reconstructed diagram with the
original finite injective diagram. -/
def boundaryReconstructionComponent (F : FiniteInjectiveBoundaryDiagram k T)
    (q : (BoundaryIndex T)ᵒᵖ) :
    (boundaryDiagram k T (posetSpaceOfBoundaryDiagram k T F)).obj q ≅
      F.obj.obj q := by
  cases q using Opposite.rec with
  | _ q =>
      cases q with
      | root => exact Iso.refl _
      | nonroot t =>
          exact (boundaryRangeLinearEquiv k T F t).toModuleIso.symm

/-- The non-root reconstruction component is inverse to range restriction,
so applying the original root map recovers the underlying root vector. -/
theorem boundaryReconstructionComponent_rootMap
    (F : FiniteInjectiveBoundaryDiagram k T) (t : T)
    (x : LinearMap.range (boundaryDiagramRootMap k T F.obj t)) :
    boundaryDiagramRootMap k T F.obj t
        ((boundaryReconstructionComponent k T F
          (op (.nonroot t : BoundaryIndex T))).hom.hom x) = x.1 := by
  change boundaryDiagramRootMap k T F.obj t
      ((boundaryRangeLinearEquiv k T F t).symm x) = x.1
  have h := (boundaryRangeLinearEquiv k T F t).apply_symm_apply x
  exact congrArg Subtype.val h

/-- The canonical isomorphism from the diagram reconstructed from ranges to
the original finite injective boundary diagram. -/
def boundaryReconstructionIso (F : FiniteInjectiveBoundaryDiagram k T) :
    boundaryDiagram k T (posetSpaceOfBoundaryDiagram k T F) ≅ F.obj :=
  NatIso.ofComponents (boundaryReconstructionComponent k T F) (by
    intro a b g
    cases a using Opposite.rec with
    | _ a =>
        cases b using Opposite.rec with
        | _ b =>
            have hba : b ≤ a := le_of_op_hom g
            cases a with
            | root =>
                cases b with
                | root =>
                    rw [show g = 𝟙 _ from Subsingleton.elim _ _]
                    simp
                | nonroot t => exact False.elim hba
            | nonroot s =>
                cases b with
                | root =>
                    rw [show g = boundaryRootArrow T s from
                      Subsingleton.elim _ _]
                    apply ModuleCat.hom_ext
                    apply LinearMap.ext
                    intro x
                    exact (boundaryReconstructionComponent_rootMap
                      k T F s x).symm
                | nonroot t =>
                    have hst : s ≤ t := hba
                    rw [show g = boundaryNonrootArrow T hst from
                      Subsingleton.elim _ _]
                    apply ModuleCat.hom_ext
                    apply LinearMap.ext
                    intro x
                    let xs : LinearMap.range
                        (boundaryDiagramRootMap k T F.obj s) := x
                    let z : LinearMap.range
                        (boundaryDiagramRootMap k T F.obj t) :=
                      ((boundaryDiagram k T
                        (posetSpaceOfBoundaryDiagram k T F)).map
                          (boundaryNonrootArrow T hst)).hom xs
                    apply F.property.2 t
                    change boundaryDiagramRootMap k T F.obj t
                        ((boundaryReconstructionComponent k T F
                          (op (.nonroot t : BoundaryIndex T))).hom.hom z) =
                      boundaryDiagramRootMap k T F.obj t
                        ((F.obj.map (boundaryNonrootArrow T hst)).hom
                          ((boundaryReconstructionComponent k T F
                            (op (.nonroot s : BoundaryIndex T))).hom.hom xs))
                    calc
                      boundaryDiagramRootMap k T F.obj t
                          ((boundaryReconstructionComponent k T F
                            (op (.nonroot t : BoundaryIndex T))).hom.hom z) =
                          z.1 :=
                        boundaryReconstructionComponent_rootMap k T F t z
                      _ = xs.1 := rfl
                      _ = boundaryDiagramRootMap k T F.obj s
                          ((boundaryReconstructionComponent k T F
                            (op (.nonroot s : BoundaryIndex T))).hom.hom xs) :=
                        (boundaryReconstructionComponent_rootMap
                          k T F s xs).symm
                      _ = boundaryDiagramRootMap k T F.obj t
                          ((F.obj.map (boundaryNonrootArrow T hst)).hom
                            ((boundaryReconstructionComponent k T F
                              (op (.nonroot s : BoundaryIndex T))).hom.hom
                                xs)) :=
                        (boundaryDiagramRootMap_map_nonroot k T F.obj hst _).symm)

instance finiteInjectiveBoundaryDiagramFunctor_essSurj :
    (finiteInjectiveBoundaryDiagramFunctor k T).EssSurj where
  mem_essImage F :=
    ⟨posetSpaceOfBoundaryDiagram k T F,
      ⟨(IsFiniteInjectiveBoundaryDiagram k T).isoMk
        (boundaryReconstructionIso k T F)⟩⟩

instance finiteInjectiveBoundaryDiagramFunctor_isEquivalence :
    (finiteInjectiveBoundaryDiagramFunctor k T).IsEquivalence where

/-- Finite `T`-spaces are exactly finite-dimensional contravariant diagrams
on the augmented boundary whose maps into the root are injective. -/
def finitePosetSpaceBoundaryEquivalence :
    Obj k T ≌ FiniteInjectiveBoundaryDiagram k T :=
  (finiteInjectiveBoundaryDiagramFunctor k T).asEquivalence

end MagnitudeConjecture.PosetSpace
