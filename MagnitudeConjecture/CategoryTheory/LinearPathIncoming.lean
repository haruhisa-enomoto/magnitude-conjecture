import MagnitudeConjecture.CategoryTheory.LinearPathCategory
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.LinearAlgebra.StdBasis

/-!
# Freeness of the incoming-arrow map in a linear path category

A family of free-path morphisms followed by distinct arrows into a fixed
target has a unique expression.  This is the path-basis input used to identify
the middle kernel in a mesh-simple presentation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.LinearPathCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- Reversed quiver arrows whose represented categorical maps end at `z`. -/
abbrev IncomingArrow (z : Q) := Σ y : Q, z ⟶ y

variable [∀ z : Q, Fintype (IncomingArrow z)]

/-- One free-path coefficient before every arrow into `z`. -/
abbrev IncomingCoefficient (x z : Q) :=
  ∀ a : IncomingArrow z, obj k Q x ⟶ obj k Q a.1

/-- Sum a family of free-path coefficients followed by the corresponding
arrows into the target. -/
def incomingSum {x z : Q} (c : IncomingCoefficient (k := k) x z) :
    obj k Q x ⟶ obj k Q z :=
  ∑ a : IncomingArrow z, c a ≫ pathHom a.2.toPath

/-- A free-path coefficient family supported at one incoming arrow. -/
def singleIncomingCoefficient {x z : Q} (a₀ : IncomingArrow z)
    (f : obj k Q x ⟶ obj k Q a₀.1) : IncomingCoefficient (k := k) x z := by
  classical
  exact fun a ↦ if h : a₀ = a then
      f ≫ eqToHom (congrArg (fun b : IncomingArrow z ↦ obj k Q b.1) h)
    else 0

/-- Summing a family supported at one incoming arrow recovers the displayed
composite. -/
@[simp]
theorem incomingSum_single {x z : Q} (a₀ : IncomingArrow z)
    (f : obj k Q x ⟶ obj k Q a₀.1) :
    incomingSum (singleIncomingCoefficient (k := k) a₀ f) =
      f ≫ pathHom a₀.2.toPath := by
  classical
  rw [incomingSum, Finset.sum_eq_single a₀]
  · simp [singleIncomingCoefficient]
    rfl
  · intro a _ ha
    simp [singleIncomingCoefficient, Ne.symm ha]
  · simp

/-- The incoming-arrow sum as a linear map. -/
def incomingSumLinearMap (x z : Q) :
    IncomingCoefficient (k := k) x z →ₗ[k] (obj k Q x ⟶ obj k Q z) where
  toFun := incomingSum
  map_add' := by
    intro c d
    simp [incomingSum, Preadditive.add_comp, Finset.sum_add_distrib]
  map_smul' := by
    intro r c
    simp [incomingSum, CategoryTheory.Linear.smul_comp, Finset.smul_sum]

@[simp]
theorem incomingSumLinearMap_apply {x z : Q}
    (c : IncomingCoefficient (k := k) x z) :
    incomingSumLinearMap (k := k) x z c = incomingSum c :=
  rfl

/-- Prefix a reverse-quiver path by the reverse of one incoming categorical
arrow. -/
def prependIncomingPath {x z : Q}
    (t : Σ a : IncomingArrow z, Quiver.Path a.1 x) :
    Quiver.Path z x :=
  t.1.2.toPath.comp t.2

omit [(z : Q) → Fintype (IncomingArrow z)] in
/-- Distinct incoming arrows followed by arbitrary tails produce distinct
paths. -/
theorem prependIncomingPath_injective (x z : Q) :
    Function.Injective (prependIncomingPath (Q := Q) (x := x) (z := z)) := by
  rintro ⟨⟨y, a⟩, p⟩ ⟨⟨y', a'⟩, p'⟩ h
  have hvertices := congrArg Quiver.Path.vertices h
  have htail : p.vertices = p'.vertices := by
    simpa [prependIncomingPath] using hvertices
  have hyy' : y = y' := by
    have hhead := congrArg List.head? htail
    simpa using hhead
  subst y'
  have hparts := (Quiver.Path.comp_inj' (p₁ := a.toPath)
    (p₂ := a'.toPath) (by simp)).1 h
  have haa' : a = a' := by
    injection hparts.1
  subst a'
  have hpp' : p = p' := hparts.2
  subst p'
  rfl

/-- The prefix operation as an embedding of path indices. -/
def prependIncomingPathEmbedding (x z : Q) :
    (Σ a : IncomingArrow z, Quiver.Path a.1 x) ↪ Quiver.Path z x :=
  ⟨prependIncomingPath, prependIncomingPath_injective x z⟩

/-- The product path basis on the domain of the incoming-arrow map. -/
def incomingCoefficientBasis (x z : Q) :
    Module.Basis (Σ a : IncomingArrow z, Quiver.Path a.1 x) k
      (IncomingCoefficient (k := k) x z) :=
  Pi.basis fun a ↦ homPathBasis (obj k Q x) (obj k Q a.1)

/-- An incoming product-basis vector maps to the corresponding prefixed path
basis vector. -/
theorem incomingSumLinearMap_basis (x z : Q)
    (t : Σ a : IncomingArrow z, Quiver.Path a.1 x) :
    incomingSumLinearMap (k := k) x z (incomingCoefficientBasis (k := k) x z t) =
      pathHom (prependIncomingPath t) := by
  classical
  rcases t with ⟨a, p⟩
  rw [show incomingCoefficientBasis (k := k) x z ⟨a, p⟩ =
      Pi.single a (homPathBasis (obj k Q x) (obj k Q a.1) p) by
    exact Pi.basis_apply _ _]
  let d : IncomingCoefficient (k := k) x z :=
    Pi.single a (homPathBasis (obj k Q x) (obj k Q a.1) p)
  change (∑ b, d b ≫ pathHom b.2.toPath) = _
  rw [Finset.sum_eq_single a]
  · simp [d, prependIncomingPath, pathHom_comp]
    rfl
  · intro b _ hba
    simp [d, hba]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- The free incoming-arrow map is injective. -/
theorem incomingSumLinearMap_injective (x z : Q) :
    Function.Injective (incomingSumLinearMap (k := k) x z) := by
  apply LinearMap.injective_of_linearIndependent
    (incomingCoefficientBasis (k := k) x z).span_eq
  have hli := (homPathBasis (obj k Q x) (obj k Q z)).linearIndependent.comp
    (prependIncomingPathEmbedding (Q := Q) x z)
    (prependIncomingPathEmbedding (Q := Q) x z).injective
  change LinearIndependent k (fun t ↦
    incomingSumLinearMap (k := k) x z
      (incomingCoefficientBasis (k := k) x z t))
  have hfamily :
      (fun t ↦ incomingSumLinearMap (k := k) x z
        (incomingCoefficientBasis (k := k) x z t)) =
      (fun t ↦ homPathBasis (obj k Q x) (obj k Q z)
        (prependIncomingPath t)) := by
    funext t
    rw [incomingSumLinearMap_basis, homPathBasis_apply]
    rfl
  rw [hfamily]
  change LinearIndependent k (fun t ↦ homPathBasis (obj k Q x) (obj k Q z)
    ((prependIncomingPathEmbedding (Q := Q) x z) t)) at hli
  exact hli

end MagnitudeConjecture.LinearPathCategory
