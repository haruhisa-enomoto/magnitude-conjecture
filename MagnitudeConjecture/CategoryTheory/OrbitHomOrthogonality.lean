import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Linear.LinearFunctor
import MagnitudeConjecture.CategoryTheory.IrreducibleLocalFunctor
import MagnitudeConjecture.CategoryTheory.AlmostSplitLocalFunctor
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd

/-!
# Orbit Hom formulas under translate orthogonality

Gabriel's orbit Hom formula expresses a downstairs Hom space as the direct
sum of the Hom spaces from one lift to all translates of the other.  If every
nonidentity translated Hom vanishes, the direct sum has only its identity
component.  This file proves that the canonical map from the original Hom
space is then a linear equivalence.  It is the linear-algebraic mechanism by
which separated covering windows make push-down fully faithful locally.
-/

set_option autoImplicit false
noncomputable section

open scoped DirectSum
open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w w' uC vC uD vD

variable {k : Type u} [Semiring k]
variable {G : Type v} [Group G]
variable {H : G → Type w}
variable [∀ g, AddCommMonoid (H g)] [∀ g, Module k (H g)]

/-- The inclusion of the identity-indexed summand, without exposing a
`DecidableEq G` parameter in later covering data. -/
noncomputable def identityLof : H 1 →ₗ[k] ⨁ g, H g := by
  classical
  exact DirectSum.lof k G H 1

/-- A direct sum whose components away from `i₀` are subsingletons is
linearly equivalent to its `i₀`-component. -/
noncomputable def uniqueComponentLinearEquiv
    {I : Type v} (M : I → Type w)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    (i₀ : I) (orthogonal : ∀ i, i ≠ i₀ → Subsingleton (M i)) :
    M i₀ ≃ₗ[k] ⨁ i, M i := by
  classical
  refine
    { toLinearMap := DirectSum.lof k I M i₀
      invFun := DirectSum.component k I M i₀
      left_inv := fun x ↦ DirectSum.component.lof_self k i₀ x
      right_inv := ?_ }
  intro x
  apply DirectSum.ext_component k
  intro i
  by_cases hi : i = i₀
  · subst i
    exact DirectSum.component.lof_self k i₀ (x i₀)
  · letI : Subsingleton (M i) := orthogonal i hi
    exact Subsingleton.elim _ _

/-- The data of an orbit Hom formula together with its compatibility with the
canonical map from the identity translate. -/
structure OrbitHomDecomposition (Downstairs : Type w')
    [AddCommMonoid Downstairs] [Module k Downstairs] where
  homEquiv : Downstairs ≃ₗ[k] ⨁ g, H g
  lift : H 1 →ₗ[k] Downstairs
  homEquiv_lift : ∀ f,
    homEquiv (lift f) = identityLof (k := k) (H := H) f

variable {Downstairs : Type w'}
variable [AddCommMonoid Downstairs] [Module k Downstairs]

namespace OrbitHomDecomposition

/-- Translate orthogonality makes the canonical identity-component map
injective. -/
theorem lift_injective
    (D : OrbitHomDecomposition (k := k) (H := H) Downstairs) :
    Function.Injective D.lift := by
  classical
  intro f g hfg
  apply DirectSum.of_injective (1 : G)
  change DirectSum.lof k G H 1 f = DirectSum.lof k G H 1 g
  change identityLof (k := k) (H := H) f = identityLof (k := k) (H := H) g
  rw [← D.homEquiv_lift,
    ← D.homEquiv_lift, hfg]

/-- If all nonidentity translated Hom spaces vanish, the canonical
identity-component map is surjective. -/
theorem lift_surjective_of_orthogonal
    (D : OrbitHomDecomposition (k := k) (H := H) Downstairs)
    (orthogonal : ∀ g : G, g ≠ 1 → Subsingleton (H g)) :
    Function.Surjective D.lift := by
  intro d
  let E : H 1 ≃ₗ[k] ⨁ g, H g :=
    uniqueComponentLinearEquiv (k := k) H 1 orthogonal
  obtain ⟨f, hf⟩ := E.surjective (D.homEquiv d)
  refine ⟨f, D.homEquiv.injective ?_⟩
  rw [D.homEquiv_lift]
  exact hf

/-- Under translate orthogonality, the canonical map appearing in the orbit
Hom formula is a linear equivalence. -/
noncomputable def liftLinearEquivOfOrthogonal
    (D : OrbitHomDecomposition (k := k) (H := H) Downstairs)
    (orthogonal : ∀ g : G, g ≠ 1 → Subsingleton (H g)) :
    H 1 ≃ₗ[k] Downstairs :=
  LinearEquiv.ofBijective D.lift
    ⟨D.lift_injective, D.lift_surjective_of_orthogonal orthogonal⟩

@[simp]
theorem liftLinearEquivOfOrthogonal_apply
    (D : OrbitHomDecomposition (k := k) (H := H) Downstairs)
    (orthogonal : ∀ g : G, g ≠ 1 → Subsingleton (H g)) (f : H 1) :
    D.liftLinearEquivOfOrthogonal orthogonal f = D.lift f :=
  rfl

/-- Bijective form used to install local fullness and faithfulness of a
push-down functor on a separated window. -/
theorem lift_bijective_of_orthogonal
    (D : OrbitHomDecomposition (k := k) (H := H) Downstairs)
    (orthogonal : ∀ g : G, g ≠ 1 → Subsingleton (H g)) :
    Function.Bijective D.lift :=
  ⟨D.lift_injective, D.lift_surjective_of_orthogonal orthogonal⟩

end OrbitHomDecomposition

section Functor
open QuotientSubmoduleEquidistribution

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable (F : C ⥤ D)
variable (K : C → C → G → Type w)
variable [∀ X Y g, AddCommMonoid (K X Y g)]
variable [∀ X Y g, Module k (K X Y g)]

/-- A Gabriel-shaped orbit Hom formula for every pair of objects of a source
category.  `sourceEquiv` identifies the identity summand with the original
Hom space, and `map_compat` says that inclusion of that summand is the functor's
map on morphisms. -/
structure FunctorOrbitHomDecomposition where
  sourceEquiv : ∀ X Y, (X ⟶ Y) ≃ₗ[k] K X Y 1
  homDecomposition : ∀ X Y,
    OrbitHomDecomposition (k := k) (H := K X Y) (F.obj X ⟶ F.obj Y)
  map_compat : ∀ X Y (f : X ⟶ Y),
    (homDecomposition X Y).lift (sourceEquiv X Y f) = F.map f

/-- Every nonidentity translate Hom summand vanishes.  When `C` is the full
subcategory on a covering window, this is the pairwise separation condition
needed for local full faithfulness. -/
def TranslateHomOrthogonal : Prop :=
  ∀ (X Y : C) (g : G), g ≠ 1 → Subsingleton (K X Y g)

namespace FunctorOrbitHomDecomposition

variable {F K}

/-- If the nonidentity summands in the orbit formula for `End(X)` vanish,
then the functor identifies the endomorphism rings of `X` and `F.obj X`.
Unlike global local full faithfulness, this needs orthogonality only for the
single pair `(X, X)`. -/
noncomputable def endRingEquivOfEndOrthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K) (X : C)
    (orthogonal : ∀ g : G, g ≠ 1 → Subsingleton (K X X g)) :
    End X ≃+* End (F.obj X) where
  toFun := F.map
  invFun := fun f ↦ (E.sourceEquiv X X).symm
    (((E.homDecomposition X X).liftLinearEquivOfOrthogonal orthogonal).symm f)
  left_inv f := by
    apply (E.sourceEquiv X X).injective
    simp only [LinearEquiv.apply_symm_apply]
    apply ((E.homDecomposition X X).liftLinearEquivOfOrthogonal
      orthogonal).injective
    rw [LinearEquiv.apply_symm_apply]
    simpa only [OrbitHomDecomposition.liftLinearEquivOfOrthogonal_apply] using
      (E.map_compat X X f).symm
  right_inv f := by
    change F.map
        ((E.sourceEquiv X X).symm
          (((E.homDecomposition X X).liftLinearEquivOfOrthogonal orthogonal).symm f)) =
      f
    rw [← E.map_compat]
    rw [LinearEquiv.apply_symm_apply]
    simpa only [OrbitHomDecomposition.liftLinearEquivOfOrthogonal_apply] using
      LinearEquiv.apply_symm_apply
        ((E.homDecomposition X X).liftLinearEquivOfOrthogonal orthogonal) f
  map_add' f g := by
    let L := (E.homDecomposition X X).liftLinearEquivOfOrthogonal orthogonal
    have hmap (h : End X) : L (E.sourceEquiv X X h) = F.map h := by
      simpa only [L, OrbitHomDecomposition.liftLinearEquivOfOrthogonal_apply] using
        E.map_compat X X h
    calc
      F.map (f + g) = L (E.sourceEquiv X X (f + g)) := (hmap (f + g)).symm
      _ = L (E.sourceEquiv X X f + E.sourceEquiv X X g) :=
        congrArg L ((E.sourceEquiv X X).map_add f g)
      _ = L (E.sourceEquiv X X f) + L (E.sourceEquiv X X g) :=
        L.map_add _ _
      _ = F.map f + F.map g := by rw [hmap, hmap]
  map_mul' f g := F.map_comp g f

@[simp]
theorem endRingEquivOfEndOrthogonal_apply
    (E : FunctorOrbitHomDecomposition (k := k) F K) (X : C)
    (orthogonal : ∀ g : G, g ≠ 1 → Subsingleton (K X X g))
    (f : End X) :
    E.endRingEquivOfEndOrthogonal X orthogonal f = F.map f :=
  rfl

/-- Self-translate orthogonality preserves an object with local endomorphism
ring as an indecomposable object downstairs. -/
theorem indecomposable_map_of_end_orthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K) (X : C)
    (orthogonal : ∀ g : G, g ≠ 1 → Subsingleton (K X X g))
    [IsLocalRing (End X)] [Limits.HasBinaryBiproducts D] :
    Indecomposable (F.obj X) := by
  letI : IsLocalRing (End (F.obj X)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (E.endRingEquivOfEndOrthogonal X orthogonal)
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end
    (F.obj X)

/-- Pairwise translate orthogonality turns the orbit Hom formula into a linear
equivalence between each source and image Hom space. -/
noncomputable def mapLinearEquivOfOrthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K)
    (orthogonal : TranslateHomOrthogonal K) (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) :=
  (E.sourceEquiv X Y).trans
    ((E.homDecomposition X Y).liftLinearEquivOfOrthogonal
      (orthogonal X Y))

@[simp]
theorem mapLinearEquivOfOrthogonal_apply
    (E : FunctorOrbitHomDecomposition (k := k) F K)
    (orthogonal : TranslateHomOrthogonal K) {X Y : C} (f : X ⟶ Y) :
    E.mapLinearEquivOfOrthogonal orthogonal X Y f = F.map f :=
  E.map_compat X Y f

/-- On every pair of source objects, the functor map is bijective. -/
theorem map_bijective_of_orthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K)
    (orthogonal : TranslateHomOrthogonal K) (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  constructor
  · intro f g hfg
    apply (E.mapLinearEquivOfOrthogonal orthogonal X Y).injective
    simpa using hfg
  · intro h
    obtain ⟨f, hf⟩ :=
      (E.mapLinearEquivOfOrthogonal orthogonal X Y).surjective h
    exact ⟨f, by simpa using hf⟩

/-- The actual Mathlib fullness instance supplied by an orthogonal orbit Hom
decomposition. -/
theorem fullOfOrthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K)
    (orthogonal : TranslateHomOrthogonal K) : F.Full where
  map_surjective :=
    (E.map_bijective_of_orthogonal orthogonal _ _).surjective

/-- Inclusion of the identity translate is injective before any orthogonality
hypothesis is imposed. -/
theorem map_injective
    (E : FunctorOrbitHomDecomposition (k := k) F K) (X Y : C) :
    Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  intro f g hfg
  apply (E.sourceEquiv X Y).injective
  apply (E.homDecomposition X Y).lift_injective
  simpa only [E.map_compat] using hfg

/-- Every functor carrying a Gabriel-shaped orbit Hom decomposition is
faithful; translate orthogonality is needed only for fullness. -/
theorem faithful
    (E : FunctorOrbitHomDecomposition (k := k) F K) : F.Faithful where
  map_injective := fun {X Y} ↦ E.map_injective X Y

/-- The orbit Hom formula and translate orthogonality feed directly into the
local irreducibility-transport theorem. -/
theorem isIrreducibleMorphism_map_iff_of_orthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K)
    (orthogonal : TranslateHomOrthogonal K)
    {X Y : C} {f : X ⟶ Y}
    (hclosed : MagnitudeConjecture.IsLocallyFactorizationClosedAt F f) :
    IsIrreducibleMorphism (F.map f) ↔ IsIrreducibleMorphism f := by
  letI : F.Full := E.fullOfOrthogonal orthogonal
  letI : F.Faithful := E.faithful
  exact
    MagnitudeConjecture.isIrreducibleMorphism_map_iff_of_locallyFactorizationClosed
      F hclosed

/-- The same local full-faithfulness mechanism preserves a right almost-split
map once the relevant incoming objects lie in the controlled image. -/
theorem rightAlmostSplit_map_of_orthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K)
    (orthogonal : TranslateHomOrthogonal K)
    {X Y : C} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit f)
    (hclosed : MagnitudeConjecture.IsLocallyRightObjectClosedAt F Y) :
    IsRightAlmostSplit (F.map f) := by
  letI : F.Full := E.fullOfOrthogonal orthogonal
  letI : F.Faithful := E.faithful
  exact
    MagnitudeConjecture.rightAlmostSplit_map_of_full_faithful_of_locallyRightObjectClosed
      F hf hclosed

/-- Dual local almost-split transport from the orthogonal orbit Hom formula. -/
theorem leftAlmostSplit_map_of_orthogonal
    (E : FunctorOrbitHomDecomposition (k := k) F K)
    (orthogonal : TranslateHomOrthogonal K)
    {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f)
    (hclosed : MagnitudeConjecture.IsLocallyLeftObjectClosedAt F X) :
    IsLeftAlmostSplit (F.map f) := by
  letI : F.Full := E.fullOfOrthogonal orthogonal
  letI : F.Faithful := E.faithful
  exact
    MagnitudeConjecture.leftAlmostSplit_map_of_full_faithful_of_locallyLeftObjectClosed
      F hf hclosed

end FunctorOrbitHomDecomposition

end Functor

end MagnitudeConjecture.CoveringHom
