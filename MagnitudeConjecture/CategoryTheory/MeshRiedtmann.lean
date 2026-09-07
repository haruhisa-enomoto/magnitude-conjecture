import MagnitudeConjecture.CategoryTheory.MeshAdditiveHull

/-!
# Riedtmann's incoming-detection condition

Condition (b) in the Bongartz--Gabriel--Riedtmann mesh-Auslander criterion
says that every nonzero morphism out of a nonprojective mesh vertex remains
nonzero after precomposition with at least one arrow entering that vertex.
In the finite additive hull this is exactly epimorphy of the matrix of all
incoming arrows.

This file records that equivalence.  It does not assume or assert that an
arbitrary finite translation quiver satisfies the condition.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory

universe u

variable {k : Type u} [Field k]
variable {Q : Type} [Quiver Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- Riedtmann condition (b) at one vertex: every nonzero morphism out of the
vertex is detected after precomposition with one represented incoming
arrow. -/
def RiedtmannConditionBAt (z : Q) : Prop :=
  ∀ (y : Q) (u : obj (k := k) T z ⟶ obj (k := k) T y),
    u ≠ 0 →
      ∃ a : IncomingArrow z,
        T.incomingArrowHom (k := k) a ≫ u ≠ 0

/-- The global condition restricts incoming detection to the nonprojective
vertices, exactly as in Riedtmann's criterion. -/
def RiedtmannConditionB : Prop :=
  ∀ z : {z : Q // z ∉ T.projective},
    T.RiedtmannConditionBAt (k := k) z.1

set_option backward.isDefEq.respectTransparency false in
/-- Incoming detection at `z` is equivalent to epimorphy of the complete
incoming-arrow matrix in the finite additive hull. -/
theorem riedtmannConditionBAt_iff_epi_additiveIncomingMap (z : Q) :
    T.RiedtmannConditionBAt (k := k) z ↔
      Epi (T.additiveIncomingMap (k := k) z) := by
  constructor
  · intro hdetect
    apply Preadditive.epi_of_cancel_zero
    intro W f hf
    apply Mat_.hom_ext
    rintro ⟨⟩ j
    apply InducedCategory.hom_ext
    let u : obj (k := k) T z ⟶ obj (k := k) T (W.X j) :=
      (f PUnit.unit j).hom
    by_contra hu
    obtain ⟨a, ha⟩ := hdetect (W.X j) u hu
    have hentry := congrFun (congrFun hf a) j
    change
      (T.additiveIncomingMap (k := k) z ≫ f) a j = 0 at hentry
    rw [Mat_.comp_apply] at hentry
    change (∑ i : PUnit,
      T.additiveIncomingMap (k := k) z a i ≫ f i j) = 0 at hentry
    rw [Fintype.sum_unique] at hentry
    apply ha
    exact congrArg InducedCategory.Hom.hom hentry
  · intro hepi y u hu
    let f : T.additiveVertexObj (k := k) z ⟶
        T.additiveVertexObj (k := k) y :=
      (T.additiveVertexHomLinearEquiv (k := k) z y).symm u
    by_contra hnone
    push Not at hnone
    have hcomp : T.additiveIncomingMap (k := k) z ≫ f = 0 := by
      apply Mat_.hom_ext
      intro a j
      change (∑ i : PUnit,
        T.additiveIncomingMap (k := k) z a i ≫ f i j) = 0
      rw [Fintype.sum_unique]
      cases j
      apply InducedCategory.hom_ext
      change T.incomingArrowHom (k := k) a ≫ u = 0
      exact hnone a
    have hf : f = 0 := by
      exact (Preadditive.epi_iff_cancel_zero
        (T.additiveIncomingMap (k := k) z)).1 hepi _ f hcomp
    apply hu
    calc
      u = T.additiveVertexHomLinearEquiv (k := k) z y f := by
        symm
        simpa only [f] using
          (T.additiveVertexHomLinearEquiv (k := k) z y).apply_symm_apply u
      _ = T.additiveVertexHomLinearEquiv (k := k) z y 0 :=
        congrArg (T.additiveVertexHomLinearEquiv (k := k) z y) hf
      _ = 0 := map_zero _

/-- Riedtmann condition (b) is equivalently epimorphy of every
nonprojective incoming-arrow matrix. -/
theorem riedtmannConditionB_iff_epi_additiveIncomingMap :
    T.RiedtmannConditionB (k := k) ↔
      ∀ z : {z : Q // z ∉ T.projective},
        Epi (T.additiveIncomingMap (k := k) z.1) := by
  constructor
  · intro h z
    exact (T.riedtmannConditionBAt_iff_epi_additiveIncomingMap
      (k := k) z.1).1 (h z)
  · intro h z
    exact (T.riedtmannConditionBAt_iff_epi_additiveIncomingMap
      (k := k) z.1).2 (h z)

/-- Composition followed by a linear form, regarded as the linear map from
the left Hom space to the coefficient dual of the right Hom space. -/
def compositionDualityLinearMap (p x j : Q)
    (epsilon : (obj (k := k) T p ⟶ obj (k := k) T j) →ₗ[k] k) :
    (obj (k := k) T p ⟶ obj (k := k) T x) →ₗ[k]
      Module.Dual k (obj (k := k) T x ⟶ obj (k := k) T j) where
  toFun f :=
    { toFun := fun g ↦ epsilon (f ≫ g)
      map_add' := by
        intro g h
        simp
      map_smul' := by
        intro r g
        simp }
  map_add' := by
    intro f g
    ext h
    simp
  map_smul' := by
    intro r f
    ext g
    simp

/-- The perfect-composition-pairing data in Riedtmann condition (c) for one
projective vertex. -/
structure RiedtmannProjectiveDualityData (p : Q) where
  dualVertex : Q
  epsilon :
    (obj (k := k) T p ⟶ obj (k := k) T dualVertex) →ₗ[k] k
  pairing_bijective : ∀ x : Q,
    Function.Bijective
      (T.compositionDualityLinearMap (k := k)
        p x dualVertex epsilon)

/-- Riedtmann condition (c): every projective vertex admits a vertex and a
linear form whose composition pairing is a vector-space duality at every
vertex. -/
def RiedtmannConditionC : Prop :=
  ∀ p : Q, p ∈ T.projective →
    Nonempty (T.RiedtmannProjectiveDualityData (k := k) p)

end RightMeshData

end MagnitudeConjecture.MeshCategory
