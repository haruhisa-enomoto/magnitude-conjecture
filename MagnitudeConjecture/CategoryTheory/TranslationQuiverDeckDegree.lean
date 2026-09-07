import MagnitudeConjecture.CategoryTheory.TranslationQuiverDeckAction
import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalGrading

/-!
# Integer degree of deck transformations

The signed augmented-walk degree is additive on the concrete fundamental
group and records the translation of vertex degree under the deck action.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe v w

variable {Q : Type v} [Quiver.{w} Q]

/-- Signed walk degree as a homomorphism from the fundamental group to the
additive integers, presented multiplicatively. -/
def fundamentalDegree (T : RightMeshData Q) (x₀ : Q) :
    FundamentalGroup T x₀ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (classDegree T x₀ g)
  map_one' := rfl
  map_mul' g h := by
    induction g, h using Quotient.inductionOn₂ with
    | _ p q =>
        change walkDegree T (p.comp q) =
          walkDegree T p + walkDegree T q
        exact walkDegree_comp T p q

@[simp]
theorem fundamentalDegree_loopClass (T : RightMeshData Q) (x₀ : Q)
    (p : Walk T x₀ x₀) :
    (fundamentalDegree T x₀ (loopClass T x₀ p)).toAdd =
      walkDegree T p :=
  rfl

/-- A deck transformation translates universal-cover vertex degree by its
own signed loop degree. -/
@[simp]
theorem vertexDegree_smul (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) (W : Vertex T x₀) :
    vertexDegree T x₀ (g • W) =
      (fundamentalDegree T x₀ g).toAdd + vertexDegree T x₀ W := by
  rcases W with ⟨y, W⟩
  induction g, W using Quotient.inductionOn₂ with
  | _ p q =>
      change walkDegree T (p.comp q) =
        walkDegree T p + walkDegree T q
      exact walkDegree_comp T p q

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
