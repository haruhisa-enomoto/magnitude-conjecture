import MagnitudeConjecture.CategoryTheory.DeckShiftAction

/-!
# Restricting coherent deck shifts to subgroups

A coherent inverse deck-translation action restricts along every subgroup.
The restricted `ShiftMkCore` uses the same ambient shift functors and
coherence isomorphisms at the included degrees.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]

/-- Restriction of a coherent shift core along a subgroup inclusion. -/
def restrictCore (D : CoherentDeckShift C G) (N : Subgroup G) :
    ShiftMkCore C (Additive N) where
  F n := D.core.F (Additive.ofMul (n.toMul : G))
  zero := D.core.zero
  add n m := D.core.add
    (Additive.ofMul (n.toMul : G)) (Additive.ofMul (m.toMul : G))
  assoc_hom_app m₁ m₂ m₃ X := D.core.assoc_hom_app
    (Additive.ofMul (m₁.toMul : G))
    (Additive.ofMul (m₂.toMul : G))
    (Additive.ofMul (m₃.toMul : G)) X
  zero_add_hom_app n X := D.core.zero_add_hom_app
    (Additive.ofMul (n.toMul : G)) X
  add_zero_hom_app n X := D.core.add_zero_hom_app
    (Additive.ofMul (n.toMul : G)) X

/-- Restriction of coherent inverse deck translations to a subgroup. -/
def restrict (D : CoherentDeckShift C G) (N : Subgroup G) :
    CoherentDeckShift C N where
  core := D.restrictCore N
  objIso n X := D.objIso (n : G) X

instance restrict_additive
    [Preadditive C]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    (N : Subgroup G) (a : Additive N) :
    ((D.restrict N).core.F a).Additive := by
  change (D.core.F (Additive.ofMul (a.toMul : G))).Additive
  infer_instance

instance restrict_linear
    {k : Type*} [Semiring k] [Preadditive C] [CategoryTheory.Linear k C]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Linear k]
    (N : Subgroup G) (a : Additive N) :
    ((D.restrict N).core.F a).Linear k := by
  change (D.core.F (Additive.ofMul (a.toMul : G))).Linear k
  infer_instance

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
