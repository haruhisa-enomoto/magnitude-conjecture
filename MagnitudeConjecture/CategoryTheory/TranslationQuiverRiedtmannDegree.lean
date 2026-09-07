import MagnitudeConjecture.CategoryTheory.TranslationQuiverSectionalPathTree
import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalGrading

/-!
# Degree normal form on a Riedtmann repetition quiver

The signed augmented-walk degree on the repetition of the sectional-prefix
tree is the difference of the explicit vertex degrees.  This is the integer
coordinate used when the finite periodic tree is contracted to one loop.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData.SectionalPath

universe u v

variable {Q : Type u} [Quiver.{v} Q]
variable {T : RightMeshData Q} (x₀ : Q)

open MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

/-- The sectional repetition degree, with its domain presented as the
augmented-quiver vertex synonym. -/
def augmentedRepetitionDegree
    (X : AugmentedVertex (orientedTree (T := T) x₀).rightMeshData) : ℤ :=
  repetitionDegree (T := T) x₀
    (show (orientedTree (T := T) x₀).Vertex from X)

set_option backward.isDefEq.respectTransparency false in
/-- On the repetition of the sectional-prefix tree, augmented-walk degree is
the difference of the canonical endpoint degrees. -/
theorem repetition_walkDegree_eq
    {X Y : AugmentedVertex (orientedTree (T := T) x₀).rightMeshData}
    (p : Walk (orientedTree (T := T) x₀).rightMeshData X Y) :
    walkDegree (orientedTree (T := T) x₀).rightMeshData p =
      augmentedRepetitionDegree (T := T) x₀ Y -
        augmentedRepetitionDegree (T := T) x₀ X := by
  induction p with
  | nil =>
      change 0 = augmentedRepetitionDegree (T := T) x₀ X -
        augmentedRepetitionDegree (T := T) x₀ X
      omega
  | @cons b c p e ih =>
      change walkDegree (orientedTree (T := T) x₀).rightMeshData p +
          arrowDegree (orientedTree (T := T) x₀).rightMeshData e =
        augmentedRepetitionDegree (T := T) x₀ _ -
          augmentedRepetitionDegree (T := T) x₀ X
      rw [ih]
      rcases e with e | e
      · cases e with
        | old a =>
            change repetitionDegree (T := T) x₀
                  (show (orientedTree (T := T) x₀).Vertex from b) -
                repetitionDegree (T := T) x₀ _ + 1 =
              repetitionDegree (T := T) x₀
                  (show (orientedTree (T := T) x₀).Vertex from c) -
                repetitionDegree (T := T) x₀ _
            have ha : repetitionDegree (T := T) x₀
                (show (orientedTree (T := T) x₀).Vertex from c) =
              repetitionDegree (T := T) x₀
                  (show (orientedTree (T := T) x₀).Vertex from b) + 1 :=
              repetitionDegree_arrow (T := T) x₀ a
            omega
        | mesh s =>
            change repetitionDegree (T := T) x₀
                  s.1 -
                repetitionDegree (T := T) x₀ _ + 2 =
              repetitionDegree (T := T) x₀
                  ((orientedTree (T := T) x₀).tauVertex s.1) -
                repetitionDegree (T := T) x₀ _
            have hs : repetitionDegree (T := T) x₀
                ((orientedTree (T := T) x₀).tauVertex s.1) =
              repetitionDegree (T := T) x₀
                  s.1 + 2 :=
              repetitionDegree_tau (T := T) x₀ s.1
            omega
      · cases e with
        | old a =>
            change repetitionDegree (T := T) x₀
                  (show (orientedTree (T := T) x₀).Vertex from b) -
                repetitionDegree (T := T) x₀ _ - 1 =
              repetitionDegree (T := T) x₀
                  (show (orientedTree (T := T) x₀).Vertex from c) -
                repetitionDegree (T := T) x₀ _
            have ha : repetitionDegree (T := T) x₀
                (show (orientedTree (T := T) x₀).Vertex from b) =
              repetitionDegree (T := T) x₀
                  (show (orientedTree (T := T) x₀).Vertex from c) + 1 :=
              repetitionDegree_arrow (T := T) x₀ a
            omega
        | mesh s =>
            change repetitionDegree (T := T) x₀
                  ((orientedTree (T := T) x₀).tauVertex s.1) -
                repetitionDegree (T := T) x₀ _ - 2 =
              repetitionDegree (T := T) x₀
                  s.1 -
                repetitionDegree (T := T) x₀ _
            have hs : repetitionDegree (T := T) x₀
                ((orientedTree (T := T) x₀).tauVertex s.1) =
              repetitionDegree (T := T) x₀
                  s.1 + 2 :=
              repetitionDegree_tau (T := T) x₀ s.1
            omega

/-- The same endpoint formula after passing to a mesh-homotopy class. -/
theorem repetition_classDegree_eq
    {X Y : AugmentedVertex (orientedTree (T := T) x₀).rightMeshData}
    (p : Quotient (homotopySetoid
      (orientedTree (T := T) x₀).rightMeshData X Y)) :
    classDegree (orientedTree (T := T) x₀).rightMeshData X p =
      augmentedRepetitionDegree (T := T) x₀ Y -
        augmentedRepetitionDegree (T := T) x₀ X := by
  induction p using Quotient.inductionOn with
  | _ p => exact repetition_walkDegree_eq (T := T) x₀ p

end MagnitudeConjecture.MeshCategory.RightMeshData.SectionalPath
