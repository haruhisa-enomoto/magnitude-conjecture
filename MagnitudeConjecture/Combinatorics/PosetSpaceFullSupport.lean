import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpace

/-!
# Full-support envelopes of finite poset spaces

Every finite poset space embeds canonically into the poset space on the same
ambient vector space whose distinguished subspaces are all full.  This is the
elementary envelope used to reduce Iyama essential surjectivity to closure of
the restricted-Yoneda image under subobjects.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

open CategoryTheory

universe u v

variable {k T : Type u} [Field k] [PartialOrder T]

/-- The poset space on the same ambient vector space as `Y` with every
distinguished subspace equal to the full space. -/
abbrev fullSupport (Y : Obj k T) : Obj k T where
  carrier := Y.carrier
  addCommGroup := Y.addCommGroup
  module := Y.module
  finiteDimensional := Y.finiteDimensional
  subspace := fun _ ↦ ⊤
  monotone_subspace := by
    intro s t hst
    exact le_rfl

/-- Every poset space embeds into its full-support envelope by the identity
map on the ambient vector space. -/
def toFullSupport (Y : Obj k T) : Y ⟶ fullSupport Y where
  linear := (LinearMap.id : Y →ₗ[k] Y)
  map_subspace := by
    intro t x hx
    exact Submodule.mem_top

@[simp]
theorem toFullSupport_linear (Y : Obj k T) :
    (toFullSupport Y).linear = (LinearMap.id : Y →ₗ[k] Y) :=
  rfl

/-- An injective underlying linear map is a monomorphism of poset spaces. -/
theorem mono_of_linear_injective {X Y : Obj k T} (f : X ⟶ Y)
    (hf : Function.Injective f.linear) : Mono f := by
  constructor
  intro Z g h hgh
  apply Hom.ext
  apply LinearMap.ext
  intro z
  apply hf
  have happ := congrArg (fun q : Z ⟶ Y ↦ q.linear z) hgh
  exact happ

/-- A surjective underlying linear map is an epimorphism of poset spaces. -/
theorem epi_of_linear_surjective {X Y : Obj k T} (f : X ⟶ Y)
    (hf : Function.Surjective f.linear) : Epi f := by
  constructor
  intro Z g h hgh
  apply Hom.ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  have happ := congrArg (fun q : X ⟶ Z ↦ q.linear x) hgh
  exact happ

/-- The canonical map into the full-support envelope is monic. -/
theorem toFullSupport_mono (Y : Obj k T) : Mono (toFullSupport Y) :=
  mono_of_linear_injective (toFullSupport Y) (fun _ _ h ↦ h)

namespace RepresentableData

variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear k C]

/-- The essential image of a representable poset-space functor is closed
under subobjects if every monomorphism into a represented object has a
represented domain, up to isomorphism. -/
def EssentialImageClosedUnderSubobjects
    (D : RepresentableData k T C) : Prop :=
  ∀ {Y : Obj k T} {X : C} (m : Y ⟶ D.obj X), Mono m →
    ∃ Z : C, Nonempty (D.obj Z ≅ Y)

/-- Once all full-support envelopes are represented, closure of the essential
image under subobjects implies essential surjectivity. -/
theorem essSurj_of_fullSupport_of_closedUnderSubobjects
    (D : RepresentableData k T C)
    (hfull : ∀ Y : Obj k T,
      ∃ X : C, Nonempty (D.obj X ≅ fullSupport Y))
    (hclosed : D.EssentialImageClosedUnderSubobjects) :
    ∀ Y : Obj k T, ∃ X : C, Nonempty (D.obj X ≅ Y) := by
  intro Y
  obtain ⟨X, ⟨e⟩⟩ := hfull Y
  let m : Y ⟶ D.obj X := toFullSupport Y ≫ e.inv
  haveI : Mono (toFullSupport Y) := toFullSupport_mono Y
  haveI : Mono e.inv := inferInstance
  have hm : Mono m := inferInstance
  exact hclosed m hm

end RepresentableData

end MagnitudeConjecture.PosetSpace
