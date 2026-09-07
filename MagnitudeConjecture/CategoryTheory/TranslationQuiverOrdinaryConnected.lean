import MagnitudeConjecture.CategoryTheory.TranslationQuiverDeckAction

/-!
# Ordinary-arrow connectivity of a right translation quiver

If every nonprojective mesh has an ordinary arrow, its formal translation
edge can be replaced by the corresponding polarized path of length two.
Consequently augmented-walk connectedness transfers along any
vertex-surjective quiver prefunctor, without requiring that the functor
preserve translation or polarization.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe v₁ v₂ w₁ w₂

variable {Q₁ : Type v₁} [Quiver.{w₁} Q₁]
variable {Q₂ : Type v₂} [Quiver.{w₂} Q₂]

/-- The ordinary quiver included into the augmented quiver. -/
def ordinaryToAugmentedPrefunctor (T : RightMeshData Q₁) :
    Q₁ ⥤q AugmentedVertex T where
  obj x := x
  map a := AugmentedArrow.old a

/-- An ordinary arrow included positively in the symmetrified ordinary
quiver. -/
def positiveOrdinaryArrow {x y : Q₁} (a : x ⟶ y) :
    @Quiver.Hom (Quiver.Symmetrify Q₁)
      (Quiver.symmetrifyQuiver Q₁) x y :=
  Sum.inl a

/-- An ordinary arrow included negatively in the symmetrified ordinary
quiver. -/
def negativeOrdinaryArrow {x y : Q₁} (a : x ⟶ y) :
    @Quiver.Hom (Quiver.Symmetrify Q₁)
      (Quiver.symmetrifyQuiver Q₁) y x :=
  Sum.inr a

/-- Replace one positive or negative augmented arrow by an ordinary
symmetrified path.  A formal mesh edge is replaced by one chosen polarized
length-two route through that mesh. -/
def ordinaryPathOfSymmetricAugmentedArrow
    (T : RightMeshData Q₁)
    (meshNonempty : ∀ s : {s : Q₁ // s ∉ T.projective},
      Nonempty (T.MeshArrow s))
    {x y : Q₁}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    @Quiver.Path (Quiver.Symmetrify Q₁)
      (Quiver.symmetrifyQuiver Q₁) x y := by
  rcases e with e | e
  · rcases e with a | s
    · exact (positiveOrdinaryArrow a).toPath
    · let a := Classical.choice (meshNonempty s)
      exact (positiveOrdinaryArrow a.2).toPath.comp
        (positiveOrdinaryArrow ((T.arrowEquiv s a.1) a.2)).toPath
  · rcases e with a | s
    · exact (negativeOrdinaryArrow a).toPath
    · let a := Classical.choice (meshNonempty s)
      exact (negativeOrdinaryArrow ((T.arrowEquiv s a.1) a.2)).toPath.comp
        (negativeOrdinaryArrow a.2).toPath

/-- Replace every formal mesh edge in an augmented walk by an ordinary
polarized length-two path. -/
def ordinaryPathOfWalk
    (T : RightMeshData Q₁)
    (meshNonempty : ∀ s : {s : Q₁ // s ∉ T.projective},
      Nonempty (T.MeshArrow s))
    {x : Q₁} : ∀ {y : Q₁}, Walk T x y →
      @Quiver.Path (Quiver.Symmetrify Q₁)
        (Quiver.symmetrifyQuiver Q₁) x y
  | _, Quiver.Path.nil => Quiver.Path.nil
  | _, Quiver.Path.cons p e =>
      (ordinaryPathOfWalk T meshNonempty p).comp
        (ordinaryPathOfSymmetricAugmentedArrow T meshNonempty e)

/-- Augmented-walk connectedness transfers along a vertex-surjective
prefunctor of the ordinary quivers whenever source formal mesh edges admit
ordinary length-two replacements.  No compatibility with either translation
is needed. -/
theorem isWalkConnectedAt_of_ordinaryPrefunctor
    (T₁ : RightMeshData Q₁) (T₂ : RightMeshData Q₂)
    (F : Q₁ ⥤q Q₂) (x₀ : Q₁)
    (hsurjective : Function.Surjective F.obj)
    (hconnected : IsWalkConnectedAt T₁ x₀)
    (meshNonempty : ∀ s : {s : Q₁ // s ∉ T₁.projective},
      Nonempty (T₁.MeshArrow s)) :
    IsWalkConnectedAt T₂ (F.obj x₀) := by
  intro y
  obtain ⟨z, rfl⟩ := hsurjective y
  obtain ⟨p⟩ := hconnected z
  let q := ordinaryPathOfWalk T₁ meshNonempty p
  exact ⟨(ordinaryToAugmentedPrefunctor T₂).symmetrify.mapPath
    (F.symmetrify.mapPath q)⟩

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
