import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiver
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Universe lifting the ordinary quiver

The bound-quiver presentation bundle is universe-local.  The ordinary quiver
has a naturally small vertex type, so this file lifts its vertices into the
coefficient-field universe without changing arrows, paths, or the free linear
path category.  The resulting reindexing functor is a linear equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The ordinary-quiver vertex set lifted to the algebra universe. -/
abbrev OrdinaryLiftedVertex := ULift.{u} S.ProjectiveLabel

/-- Universe lifting changes only vertices, not the corresponding arrow
spaces. -/
instance ordinaryLiftedQuiver : Quiver.{u} S.OrdinaryLiftedVertex where
  Hom x y := S.OrdinaryArrow x.down y.down

noncomputable instance ordinaryLiftedVertexFintype :
    Fintype S.OrdinaryLiftedVertex :=
  Fintype.ofEquiv S.ProjectiveLabel Equiv.ulift.symm

instance ordinaryLiftedArrowFintype
    (x y : S.OrdinaryLiftedVertex) : Fintype (x ⟶ y) :=
  S.ordinaryArrowFintype x.down y.down

/-- Forget the universe lift on the ordinary quiver. -/
def ordinaryQuiverDownPrefunctor :
    S.OrdinaryLiftedVertex ⥤q S.ProjectiveLabel where
  obj x := x.down
  map a := a

/-- Lift the vertices of the small ordinary quiver. -/
def ordinaryQuiverUpPrefunctor :
    S.ProjectiveLabel ⥤q S.OrdinaryLiftedVertex where
  obj x := ULift.up x
  map a := a

@[simp]
theorem ordinaryQuiverUpDown_mapPath
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y) :
    S.ordinaryQuiverDownPrefunctor.mapPath
      (S.ordinaryQuiverUpPrefunctor.mapPath p) = p := by
  induction p with
  | nil => rfl
  | cons p a ih =>
      simp only [Prefunctor.mapPath_cons, ih]
      rfl

@[simp]
theorem ordinaryQuiverDownUp_mapPath
    {x y : S.OrdinaryLiftedVertex} (p : Quiver.Path x y) :
    S.ordinaryQuiverUpPrefunctor.mapPath
      (S.ordinaryQuiverDownPrefunctor.mapPath p) = p := by
  induction p with
  | nil => rfl
  | @cons z w p a ih =>
      rcases z with ⟨z⟩
      rcases w with ⟨w⟩
      simp only [Prefunctor.mapPath_cons, ih]
      rfl

/-- The quiver isomorphism gives a bijection between paths with the
corresponding endpoints. -/
def ordinaryLiftedPathEquiv (x y : S.OrdinaryLiftedVertex) :
    Quiver.Path x y ≃ Quiver.Path x.down y.down where
  toFun := S.ordinaryQuiverDownPrefunctor.mapPath
  invFun := S.ordinaryQuiverUpPrefunctor.mapPath
  left_inv := S.ordinaryQuiverDownUp_mapPath
  right_inv := S.ordinaryQuiverUpDown_mapPath

/-- Reindex the free linear category from lifted ordinary vertices back to
the original small vertex set. -/
def ordinaryLiftedToOrdinary :
    LinearPathCategory.Category k S.OrdinaryLiftedVertex ⥤
      LinearPathCategory.Category k S.ProjectiveLabel :=
  LinearPathCategory.lift
    (fun x ↦ LinearPathCategory.obj k S.ProjectiveLabel x.down)
    (fun {_ _} a ↦ LinearPathCategory.pathHom
      (show Quiver.Path _ _ from
        Quiver.Path.nil.cons a))

noncomputable instance ordinaryLiftedToOrdinary_additive :
    S.ordinaryLiftedToOrdinary.Additive := by
  dsimp only [ordinaryLiftedToOrdinary]
  infer_instance

noncomputable instance ordinaryLiftedToOrdinary_linear :
    S.ordinaryLiftedToOrdinary.Linear k := by
  dsimp only [ordinaryLiftedToOrdinary]
  infer_instance

/-- Path reindexing with endpoints stated as the actual images of the
free-category functor. -/
def ordinaryLiftedFunctorPathEquiv
    (X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex) :
    Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X) ≃
      Quiver.Path
        (LinearPathCategory.vertex (S.ordinaryLiftedToOrdinary.obj Y))
        (LinearPathCategory.vertex (S.ordinaryLiftedToOrdinary.obj X)) :=
  S.ordinaryLiftedPathEquiv
    (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)

@[simp]
theorem ordinaryLiftedToOrdinary_map_pathHom
    {x y : S.OrdinaryLiftedVertex} (p : Quiver.Path x y) :
    S.ordinaryLiftedToOrdinary.map (LinearPathCategory.pathHom p) =
      LinearPathCategory.pathHom (S.ordinaryLiftedPathEquiv x y p) := by
  change (LinearPathCategory.lift
    (fun x ↦ LinearPathCategory.obj k S.ProjectiveLabel x.down)
    (fun {_ _} a ↦ LinearPathCategory.pathHom
      (show Quiver.Path _ _ from
        Quiver.Path.nil.cons a))).map
      (LinearPathCategory.pathHom p) = _
  rw [LinearPathCategory.lift_map_pathHom]
  induction p with
  | nil =>
      rw [LinearPathCategory.pathMap_nil]
      change 𝟙 _ = LinearPathCategory.pathHom _
      rw [show S.ordinaryLiftedPathEquiv x x Quiver.Path.nil =
          Quiver.Path.nil by rfl,
        LinearPathCategory.pathHom_nil]
  | @cons z _ p a ih =>
      simp only [LinearPathCategory.pathMap_cons,
        ordinaryLiftedPathEquiv, ih]
      rw [LinearPathCategory.pathHom_comp]
      rfl

/-- Reindexing lifted paths gives a linear equivalence on each actual Hom
space of the reindexing functor. -/
def ordinaryLiftedHomLinearEquiv
    (X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex) :
    (X ⟶ Y) ≃ₗ[k]
      (S.ordinaryLiftedToOrdinary.obj X ⟶
        S.ordinaryLiftedToOrdinary.obj Y) :=
  (LinearPathCategory.homPathLinearEquiv X Y).trans
    ((Finsupp.domLCongr
      (S.ordinaryLiftedFunctorPathEquiv X Y)).trans
      (LinearPathCategory.homPathLinearEquiv
        (S.ordinaryLiftedToOrdinary.obj X)
        (S.ordinaryLiftedToOrdinary.obj Y)).symm)

@[simp]
theorem ordinaryLiftedHomLinearEquiv_pathHom
    {X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    S.ordinaryLiftedHomLinearEquiv X Y (LinearPathCategory.pathHom p) =
      LinearPathCategory.pathHom
        (S.ordinaryLiftedFunctorPathEquiv X Y p) := by
  rw [ordinaryLiftedHomLinearEquiv,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearPathCategory.homPathLinearEquiv_pathHom]
  have hdom :
      (Finsupp.domLCongr
        (S.ordinaryLiftedFunctorPathEquiv X Y) :
          (Quiver.Path (LinearPathCategory.vertex Y)
              (LinearPathCategory.vertex X) →₀ k) ≃ₗ[k]
            (Quiver.Path
                (LinearPathCategory.vertex
                  (S.ordinaryLiftedToOrdinary.obj Y))
                (LinearPathCategory.vertex
                  (S.ordinaryLiftedToOrdinary.obj X)) →₀ k))
          (Finsupp.single p 1) =
        Finsupp.single
          (S.ordinaryLiftedFunctorPathEquiv X Y p) 1 := by
    change Finsupp.equivMapDomain
      (S.ordinaryLiftedFunctorPathEquiv X Y)
        (Finsupp.single p 1) = _
    exact Finsupp.equivMapDomain_single _ _ _
  rw [hdom]
  rfl

/-- The Hom map of the lifted-vertex reindexing is the explicit path-basis
linear equivalence. -/
theorem ordinaryLiftedToOrdinary_map_eq_homLinearEquiv
    (X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex) :
    (S.ordinaryLiftedToOrdinary.mapLinearMap k :
      (X ⟶ Y) →ₗ[k]
        (S.ordinaryLiftedToOrdinary.obj X ⟶
          S.ordinaryLiftedToOrdinary.obj Y)) =
      (S.ordinaryLiftedHomLinearEquiv X Y).toLinearMap := by
  apply (LinearPathCategory.homPathBasis X Y).ext
  intro p
  simp only [LinearPathCategory.homPathBasis_apply]
  change S.ordinaryLiftedToOrdinary.map
      (LinearPathCategory.pathHom p) =
    S.ordinaryLiftedHomLinearEquiv X Y
      (LinearPathCategory.pathHom p)
  rw [S.ordinaryLiftedToOrdinary_map_pathHom,
    S.ordinaryLiftedHomLinearEquiv_pathHom]
  rfl

noncomputable instance ordinaryLiftedToOrdinary_full :
    S.ordinaryLiftedToOrdinary.Full where
  map_surjective {X Y} f := by
    refine ⟨(S.ordinaryLiftedHomLinearEquiv X Y).symm f, ?_⟩
    change (S.ordinaryLiftedToOrdinary.mapLinearMap k :
      (X ⟶ Y) →ₗ[k]
        (S.ordinaryLiftedToOrdinary.obj X ⟶
          S.ordinaryLiftedToOrdinary.obj Y))
        ((S.ordinaryLiftedHomLinearEquiv X Y).symm f) = f
    rw [S.ordinaryLiftedToOrdinary_map_eq_homLinearEquiv]
    exact (S.ordinaryLiftedHomLinearEquiv X Y).apply_symm_apply f

noncomputable instance ordinaryLiftedToOrdinary_faithful :
    S.ordinaryLiftedToOrdinary.Faithful where
  map_injective {X Y} f g hfg := by
    apply (S.ordinaryLiftedHomLinearEquiv X Y).injective
    let hmap := S.ordinaryLiftedToOrdinary_map_eq_homLinearEquiv X Y
    calc
      S.ordinaryLiftedHomLinearEquiv X Y f =
          S.ordinaryLiftedToOrdinary.map f :=
        (LinearMap.congr_fun hmap f).symm
      _ = S.ordinaryLiftedToOrdinary.map g := hfg
      _ = S.ordinaryLiftedHomLinearEquiv X Y g :=
        LinearMap.congr_fun hmap g

/-- The lifted-vertex reindexing is bijective on objects. -/
theorem ordinaryLiftedToOrdinary_obj_bijective :
    Function.Bijective S.ordinaryLiftedToOrdinary.obj := by
  constructor
  · rintro ⟨x⟩ ⟨y⟩ hxy
    exact congrArg ULift.up hxy
  · intro x
    exact ⟨ULift.up x, rfl⟩

noncomputable instance ordinaryLiftedToOrdinary_essSurj :
    S.ordinaryLiftedToOrdinary.EssSurj := by
  constructor
  intro Y
  obtain ⟨X, hX⟩ := S.ordinaryLiftedToOrdinary_obj_bijective.2 Y
  exact ⟨X, ⟨eqToIso hX⟩⟩

/-- Universe lifting the ordinary vertices does not change the free linear
path category. -/
noncomputable def ordinaryLiftedPathCategoryEquivalence :
    LinearPathCategory.Category k S.OrdinaryLiftedVertex ≌
      LinearPathCategory.Category k S.ProjectiveLabel := by
  let F := S.ordinaryLiftedToOrdinary
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
