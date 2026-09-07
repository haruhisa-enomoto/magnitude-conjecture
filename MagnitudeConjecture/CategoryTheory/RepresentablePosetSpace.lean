import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Linear.LinearFunctor
import MagnitudeConjecture.Combinatorics.PosetSpaceRealization

/-!
# The representable poset-space realization functor

This file formalizes the concrete functor in the frozen manuscript.  Given a
distinguished source `P`, projective objects `P_t`, and compatible maps
`P ⟶ P_t`, an object `X` is sent to the poset space with total space
`Hom(P,X)` and `t`-subspace the image of

`Hom(P_t,X) ⟶ Hom(P,X)`.

The genuinely structural part of Iyama's theorem—fullness and essential
surjectivity—is kept visible as data to be constructed from the primitive
factor, rather than postulated in the public theorem.
-/

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace MagnitudeConjecture.PosetSpace

universe u v

variable (k T : Type u) (C : Type v) [Field k] [PartialOrder T]
variable [Category.{u} C] [Preadditive C] [Linear k C]

/-- Categorical data needed to define the manuscript's representable
poset-space functor.  `factor` is the coherent form of the order relation:
when `s ≤ t`, the chosen map to `P_s` factors through the chosen map to
`P_t`. -/
structure RepresentableData where
  source : C
  projective : T → C
  unit : ∀ t, source ⟶ projective t
  factor : ∀ {s t : T}, s ≤ t →
    ∃ v : projective t ⟶ projective s, unit t ≫ v = unit s
  homFinite : ∀ X : C, Module.Finite k (source ⟶ X)

namespace RepresentableData

variable {k T C}

/-- Precomposition with the chosen map `P ⟶ P_t`. -/
def precomposition (D : RepresentableData k T C) (t : T) (X : C) :
    (D.projective t ⟶ X) →ₗ[k] (D.source ⟶ X) where
  toFun f := D.unit t ≫ f
  map_add' f g := by simp
  map_smul' a f := by simp

/-- Postcomposition with a categorical morphism. -/
def postcomposition (D : RepresentableData k T C) {X Y : C} (f : X ⟶ Y) :
    (D.source ⟶ X) →ₗ[k] (D.source ⟶ Y) where
  toFun g := g ≫ f
  map_add' g h := by simp
  map_smul' a g := by simp

/-- The representable `T`-space attached to `X`. -/
def obj (D : RepresentableData k T C) (X : C) : Obj k T := by
  letI : Module.Finite k (D.source ⟶ X) := D.homFinite X
  exact
    { carrier := D.source ⟶ X
      subspace := fun t ↦ LinearMap.range (D.precomposition t X)
      monotone_subspace := by
        intro s t hst x hx
        obtain ⟨g, rfl⟩ := hx
        obtain ⟨v, hv⟩ := D.factor hst
        refine ⟨v ≫ g, ?_⟩
        change D.unit t ≫ (v ≫ g) = D.unit s ≫ g
        rw [← Category.assoc, hv] }

/-- Postcomposition defines a morphism of representable poset spaces. -/
def map (D : RepresentableData k T C) {X Y : C} (f : X ⟶ Y) :
    D.obj X ⟶ D.obj Y where
  linear := D.postcomposition f
  map_subspace := by
    intro t x hx
    obtain ⟨g, rfl⟩ := hx
    refine ⟨g ≫ f, ?_⟩
    dsimp only [precomposition, postcomposition]
    exact (Category.assoc (D.unit t) g f).symm

@[simp]
theorem map_linear (D : RepresentableData k T C) {X Y : C} (f : X ⟶ Y) :
    (D.map f).linear = D.postcomposition f :=
  rfl

/-- The manuscript's objectwise construction is a literal functor. -/
def functor (D : RepresentableData k T C) : C ⥤ Obj k T where
  obj := D.obj
  map := D.map
  map_id X := by
    apply Hom.ext
    apply LinearMap.ext
    intro g
    change g ≫ 𝟙 X = g
    simp
  map_comp f g := by
    apply Hom.ext
    apply LinearMap.ext
    intro h
    change h ≫ (f ≫ g) = (h ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm

@[simp]
theorem functor_obj (D : RepresentableData k T C) (X : C) :
    D.functor.obj X = D.obj X :=
  rfl

@[simp]
theorem functor_map (D : RepresentableData k T C) {X Y : C} (f : X ⟶ Y) :
    D.functor.map f = D.map f :=
  rfl

instance (D : RepresentableData k T C) : D.functor.Additive where
  map_add := by
    intro X Y f g
    apply Hom.ext
    apply LinearMap.ext
    intro h
    change h ≫ (f + g) = h ≫ f + h ≫ g
    simp

instance (D : RepresentableData k T C) : D.functor.Linear k where
  map_smul f c := by
    apply Hom.ext
    apply LinearMap.ext
    intro g
    change g ≫ (c • f) = c • (g ≫ f)
    simp

/-- The total dimension of the realized poset space is exactly the dimension
of the represented Hom space. -/
theorem finrank_obj (D : RepresentableData k T C) (X : C) :
    Module.finrank k (D.obj X) = Module.finrank k (D.source ⟶ X) :=
  rfl

/-- Fullness on one object and scalar endomorphisms in the source category
make its representable poset space Schur. -/
theorem obj_isSchur
    (D : RepresentableData k T C) {X : C}
    (hnonzero : ∃ h : D.source ⟶ X, h ≠ 0)
    (hfull : ∀ f : D.obj X ⟶ D.obj X,
      ∃ g : X ⟶ X, D.map g = f)
    (hscalar : ∀ g : X ⟶ X, ∃ a : k, g = a • 𝟙 X) :
    IsSchur k T (D.obj X) := by
  constructor
  · exact hnonzero
  · intro f
    obtain ⟨g, rfl⟩ := hfull f
    obtain ⟨a, rfl⟩ := hscalar g
    refine ⟨a, ?_⟩
    change D.postcomposition (a • 𝟙 X) =
      a • (LinearMap.id : (D.source ⟶ X) →ₗ[k] (D.source ⟶ X))
    apply LinearMap.ext
    intro h
    change h ≫ (a • 𝟙 X) = a • h
    simp

/-- Faithfulness of `Hom(P,-)` in elementwise form makes the representable
poset-space functor faithful. -/
theorem map_injective
    (D : RepresentableData k T C)
    (hfaithful : ∀ {X Y : C} (f g : X ⟶ Y),
      (∀ h : D.source ⟶ X, h ≫ f = h ≫ g) → f = g)
    {X Y : C} : Function.Injective
      (D.functor.map : (X ⟶ Y) → (D.functor.obj X ⟶ D.functor.obj Y)) := by
  intro f g heq
  apply hfaithful f g
  intro h
  have hlinear := congrArg Hom.linear heq
  have happ := LinearMap.congr_fun hlinear h
  change h ≫ f = h ≫ g at happ
  exact happ

/-- The corresponding `Functor.Faithful` package. -/
theorem faithful
    (D : RepresentableData k T C)
    (hfaithful : ∀ {X Y : C} (f g : X ⟶ Y),
      (∀ h : D.source ⟶ X, h ≫ f = h ≫ g) → f = g) :
    D.functor.Faithful where
  map_injective := fun {_ _} _ _ heq ↦ D.map_injective hfaithful heq

/-- Exact extra data needed to promote the concrete representable functor to
Iyama's poset-space equivalence.  Subsequent work constructs these fields from
the literal primitive factor. -/
structure EquivalenceData (D : RepresentableData k T C) where
  full : ∀ {X Y : C} (f : D.obj X ⟶ D.obj Y),
    ∃ g : X ⟶ Y, D.map g = f
  faithful : ∀ {X Y : C} (f g : X ⟶ Y),
    D.map f = D.map g → f = g
  essSurj : ∀ Y : Obj k T, ∃ X : C, Nonempty (D.obj X ≅ Y)

namespace EquivalenceData

variable {D : RepresentableData k T C}

/-- Fullness of the concrete functor. -/
theorem functorFull (R : EquivalenceData D) : D.functor.Full where
  map_surjective := fun {_ _} f ↦ R.full f

/-- Faithfulness of the concrete functor. -/
theorem functorFaithful (R : EquivalenceData D) : D.functor.Faithful where
  map_injective := fun {_ _} f g heq ↦ R.faithful f g heq

/-- Essential surjectivity of the concrete functor. -/
theorem functorEssSurj (R : EquivalenceData D) : D.functor.EssSurj where
  mem_essImage Y := R.essSurj Y

/-- A nonzero scalar-endomorphism object is sent to a Schur poset space by
the completed realization. -/
theorem obj_isSchur (R : EquivalenceData D) {X : C}
    (hnonzero : ∃ h : D.source ⟶ X, h ≠ 0)
    (hscalar : ∀ g : X ⟶ X, ∃ a : k, g = a • 𝟙 X) :
    IsSchur k T (D.obj X) :=
  D.obj_isSchur hnonzero (fun f ↦ R.full f) hscalar

/-- The equivalence furnished by completed realization data. -/
def equivalence (R : EquivalenceData D) : C ≌ Obj k T := by
  letI : D.functor.Full := R.functorFull
  letI : D.functor.Faithful := R.functorFaithful
  letI : D.functor.EssSurj := R.functorEssSurj
  letI : D.functor.IsEquivalence := Functor.IsEquivalence.mk
  exact D.functor.asEquivalence

end EquivalenceData

end RepresentableData

end MagnitudeConjecture.PosetSpace
