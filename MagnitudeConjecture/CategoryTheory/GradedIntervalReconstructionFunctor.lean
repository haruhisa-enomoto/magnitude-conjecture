import MagnitudeConjecture.CategoryTheory.GradedIntervalReconstructedModule
import MagnitudeConjecture.CategoryTheory.GradedSupportedEvaluation

/-! # Functorial reconstruction from interval representation coordinates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable {F G : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k}
variable [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]

/-- A natural transformation acts componentwise on the reconstructed vector spaces. -/
def intervalCoordinateMap (m : ℕ) (α : F ⟶ G) :
    intervalCoordinateSpace R hmul e he0 F m →ₗ[k] intervalCoordinateSpace R hmul e he0 G m where
  toFun x p := (α.app (op (intervalProjectiveLabel R hmul e he0 m p))).hom (x p)
  map_add' x y := by funext p; exact map_add _ _ _
  map_smul' c x := by funext p; exact map_smul _ _ _

/-- Naturality is precisely compatibility with the reconstructed algebra action. -/
theorem intervalActionMap_naturality (m : ℕ) (α : F ⟶ G) (a : A)
    (x : intervalCoordinateSpace R hmul e he0 F m) :
    intervalCoordinateMap R hmul e he0 m α (intervalActionMap R hmul e he0 he F m a x) =
      intervalActionMap R hmul e he0 he G m a (intervalCoordinateMap R hmul e he0 m α x) := by
  funext p
  change (α.app (op (intervalProjectiveLabel R hmul e he0 m p))).hom
    (∑ q, (F.map (intervalActionCoefficient R hmul e he0 he m p q a).op).hom (x q)) =
      ∑ q, (G.map (intervalActionCoefficient R hmul e he0 he m p q a).op).hom
        ((α.app (op (intervalProjectiveLabel R hmul e he0 m q))).hom (x q))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact ConcreteCategory.congr_hom
    (α.naturality (intervalActionCoefficient R hmul e he0 he m p q a).op) (x q)

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0)

/-- The induced degree-zero map between the actual reconstructed modules. -/
def intervalReconstructedMap (hF : ∀ p, FiniteDimensional k (F.obj p))
    (hG : ∀ p, FiniteDimensional k (G.obj p)) (m : ℕ) (α : F ⟶ G) :
    intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hF m ⟶
      intervalReconstructedSupportedObject R hmul e he0 he G hneg h1 hsum horth hG m := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  letI := intervalReconstructedModule R hmul e he0 he G hneg h1 hsum horth m
  let f : intervalCoordinateSpace R hmul e he0 F m →ₗ[A]
      intervalCoordinateSpace R hmul e he0 G m :=
    { toFun := intervalCoordinateMap R hmul e he0 m α
      map_add' := (intervalCoordinateMap R hmul e he0 m α).map_add
      map_smul' := fun a x ↦ intervalActionMap_naturality R hmul e he0 he m α a x }
  apply ObjectProperty.homMk
  refine ⟨f, ?_⟩
  intro d x hx p hp
  change (p.2.val : ℤ) ≠ d + (0 - 0) at hp
  have hp' : (p.2.val : ℤ) ≠ d := by simpa only [sub_self, add_zero] using hp
  change (α.app (op (intervalProjectiveLabel R hmul e he0 m p))).hom (x p) = 0
  have hx' : x p = 0 := hx p hp'
  rw [hx', map_zero]

/-- Reconstructing the supported graded module is functorial in the finite representation. -/
def intervalReconstructionFunctor (m : ℕ) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := (PrincipalDegreeCategory R hmul e he0)ᵒᵖ) k ⥤ SupportedCategory (R := R) m where
  obj F := intervalReconstructedSupportedObject R hmul e he0 he F.obj.obj
    hneg h1 hsum horth F.property.1 m
  map f := intervalReconstructedMap R hmul e he0 he hneg h1 hsum horth
    _ _ m f.hom.hom
  map_id F := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    funext p
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    funext p
    rfl

instance intervalReconstructionFunctor_additive (m : ℕ) :
    (intervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    funext p
    rfl

/-- The candidate inverse to supported projective evaluation, with its support domain bundled. -/
def supportedIntervalReconstructionFunctor (m : ℕ) :
    ObjectDeletion.VanishingFiniteModuleCategory (k := k)
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) ⥤
        SupportedCategory (R := R) m :=
  (ObjectDeletion.finiteModuleVanishesOnDeleted (k := k) _
    (principalOutsideInterval R hmul e he0 m)).ι ⋙
      intervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m

instance supportedIntervalReconstructionFunctor_additive (m : ℕ) :
    (supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m).Additive := by
  unfold supportedIntervalReconstructionFunctor
  infer_instance

end MagnitudeConjecture.Graded.FiniteGradedModule
