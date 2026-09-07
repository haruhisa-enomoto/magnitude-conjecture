import MagnitudeConjecture.Algebra.StringEndpointDeterminism
import MagnitudeConjecture.Algebra.StringLeftBoundaryExtension

/-!
# Left-end hooks and cohooks for string modules

Butler--Ringel's canonical exact sequences use hook and cohook operations at
both ends of a string.  Reversal exchanges the two endpoints, so the left-end
operations are obtained from the already constructed right-end operations.
The module maps are transported through the canonical reversal isomorphisms;
no second coordinate calculation is needed.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A maximal hook at the left endpoint.  Its auxiliary result is stored in
reversed orientation so that the underlying right hook is literal. -/
structure LeftHookExtension (C : Word R) where
  reverseResult : Word R
  hook : HookExtension C.reverse reverseResult

namespace LeftHookExtension

/-- The result word in the original orientation. -/
def result {C : Word R} (hook : LeftHookExtension C) : Word R :=
  hook.reverseResult.reverse

/-- Forget maximality while retaining the positive left boundary. -/
def toLeftPositiveBoundaryExtension {C : Word R}
    (hook : LeftHookExtension C) : LeftPositiveBoundaryExtension C where
  reverseResult := hook.reverseResult
  extension := hook.hook.toPositiveBoundaryExtension

/-- Left hooks are exactly right hooks on the reversed source word, with the
auxiliary result retained in reversed orientation. -/
def asReverseHookEquiv (C : Word R) :
    LeftHookExtension C ≃ (Σ D, HookExtension C.reverse D) where
  toFun hook := ⟨hook.reverseResult, hook.hook⟩
  invFun hook := ⟨hook.1, hook.2⟩
  left_inv hook := by cases hook; rfl
  right_inv hook := by cases hook; rfl

/-- Every valid positive boundary at the reversed right endpoint gives a
maximal hook at the original left endpoint. -/
theorem exists_of_reverse_append_positive
    (hR : IsAdmissible R) (C : Word R) {z : Q}
    (a : C.reverse.target ⟶ z)
    (h : IsString R
      (C.reverse.path.comp (positiveArrow a).toPath)) :
    ∃ hook : LeftHookExtension C,
      (⟨hook.hook.vertex, hook.hook.arrow⟩ : Quiver.Star C.reverse.target) =
        ⟨z, a⟩ := by
  rcases HookExtension.exists_of_append_positive hR C.reverse a h with
    ⟨E, hook, hboundary⟩
  exact ⟨⟨E, hook⟩, hboundary⟩

/-- The number of letters added by a left hook. -/
def steps {C : Word R} (hook : LeftHookExtension C) : ℕ :=
  HookExtension.steps hook.hook

@[simp]
theorem result_length {C : Word R} (hook : LeftHookExtension C) :
    hook.result.length = C.length + hook.steps := by
  have h := HookExtension.result_length hook.hook
  simpa only [result, reverse_length, steps] using h

/-- The canonical left-hook projection, transported through word reversal. -/
def moduleMap {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) :
    hook.result.rightModule hmono ⟶ C.rightModule hmono :=
  hook.toLeftPositiveBoundaryExtension.moduleMap hmono

instance moduleMap_epi {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) : Epi (hook.moduleMap hmono) := by
  dsimp only [moduleMap]
  exact LeftPositiveBoundaryExtension.moduleMap_epi _ _

/-- Embed an occurrence of the original word into the result of a left hook.
In reversed orientation this is the ordinary prefix-position embedding. -/
def position {C : Word R} (hook : LeftHookExtension C) {x : Q}
    (i : C.PositionAt x) : hook.result.PositionAt x :=
  hook.toLeftPositiveBoundaryExtension.position i

/-- The left-hook projection is the identity on every inherited position
basis vector. -/
@[simp]
theorem moduleMap_app_single_position {C : Word R}
    (hook : LeftHookExtension C) (hmono : IsMonomial R) {x : Q}
    (i : C.PositionAt x) (c : k) :
    (hook.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single (hook.position i) c) =
      Finsupp.single i c := by
  exact hook.toLeftPositiveBoundaryExtension.moduleMap_app_single_position
    hmono i c

/-- A left hook witnesses that the original word does not end on a peak. -/
theorem not_endsOnPeak {C : Word R} (hook : LeftHookExtension C) :
    ¬ C.EndsOnPeak :=
  hook.hook.not_startsOnPeak

/-- In a special-biserial presentation, the result of a left hook is uniquely
determined by its reversed positive boundary arrow. -/
theorem result_eq_of_boundary_eq
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : SpecialBiserialPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (hook₁ hook₂ : LeftHookExtension C)
    (hboundary :
      (⟨hook₁.hook.vertex, hook₁.hook.arrow⟩ :
        Quiver.Star C.reverse.target) =
        ⟨hook₂.hook.vertex, hook₂.hook.arrow⟩) :
    hook₁.result = hook₂.result := by
  have hpairs := HookExtension.eq_of_boundary_eq P
    hook₁.hook hook₂.hook hboundary
  have hreversed : hook₁.reverseResult = hook₂.reverseResult :=
    congrArg Sigma.fst hpairs
  exact congrArg (fun E : Word P.toPresentation.relations ↦ E.reverse)
    hreversed

/-- Maximal left hooks are in bijection with the valid positive boundary
arrows at the reversed right endpoint. -/
def boundaryEquiv
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) :
    LeftHookExtension C ≃ C.reverse.PositiveAppendArrow :=
  (asReverseHookEquiv C).trans (HookExtension.boundaryEquiv P C.reverse)

end LeftHookExtension

/-- A maximal cohook at the left endpoint.  Its auxiliary result is stored in
reversed orientation so that the underlying right cohook is literal. -/
structure LeftCohookExtension (C : Word R) where
  reverseResult : Word R
  cohook : CohookExtension C.reverse reverseResult

namespace LeftCohookExtension

/-- The result word in the original orientation. -/
def result {C : Word R} (cohook : LeftCohookExtension C) : Word R :=
  cohook.reverseResult.reverse

/-- Forget maximality while retaining the negative left boundary. -/
def toLeftNegativeBoundaryExtension {C : Word R}
    (cohook : LeftCohookExtension C) : LeftNegativeBoundaryExtension C where
  reverseResult := cohook.reverseResult
  extension := cohook.cohook.toNegativeBoundaryExtension

/-- Left cohooks are exactly right cohooks on the reversed source word, with
the auxiliary result retained in reversed orientation. -/
def asReverseCohookEquiv (C : Word R) :
    LeftCohookExtension C ≃ (Σ D, CohookExtension C.reverse D) where
  toFun cohook := ⟨cohook.reverseResult, cohook.cohook⟩
  invFun cohook := ⟨cohook.1, cohook.2⟩
  left_inv cohook := by cases cohook; rfl
  right_inv cohook := by cases cohook; rfl

/-- Every valid negative boundary at the reversed right endpoint gives a
maximal cohook at the original left endpoint. -/
theorem exists_of_reverse_append_negative
    (hR : IsAdmissible R) (C : Word R) {z : Q}
    (a : z ⟶ C.reverse.target)
    (h : IsString R
      (C.reverse.path.comp (negativeArrow a).toPath)) :
    ∃ cohook : LeftCohookExtension C,
      (⟨cohook.cohook.vertex, cohook.cohook.arrow⟩ :
        Quiver.Costar C.reverse.target) =
        ⟨z, a⟩ := by
  rcases CohookExtension.exists_of_append_negative hR C.reverse a h with
    ⟨E, cohook, hboundary⟩
  exact ⟨⟨E, cohook⟩, hboundary⟩

/-- The number of letters added by a left cohook. -/
def steps {C : Word R} (cohook : LeftCohookExtension C) : ℕ :=
  CohookExtension.steps cohook.cohook

@[simp]
theorem result_length {C : Word R} (cohook : LeftCohookExtension C) :
    cohook.result.length = C.length + cohook.steps := by
  have h := CohookExtension.result_length cohook.cohook
  simpa only [result, reverse_length, steps] using h

/-- The canonical left-cohook inclusion, transported through word reversal. -/
def moduleMap {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) :
    C.rightModule hmono ⟶ cohook.result.rightModule hmono :=
  cohook.toLeftNegativeBoundaryExtension.moduleMap hmono

instance moduleMap_mono {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) : Mono (cohook.moduleMap hmono) := by
  dsimp only [moduleMap]
  exact LeftNegativeBoundaryExtension.moduleMap_mono _ _

/-- Embed an occurrence of the original word into the result of a left
cohook.  In reversed orientation this is the ordinary prefix-position
embedding. -/
def position {C : Word R} (cohook : LeftCohookExtension C) {x : Q}
    (i : C.PositionAt x) : cohook.result.PositionAt x :=
  cohook.toLeftNegativeBoundaryExtension.position i

/-- The left-cohook inclusion carries every original position basis vector
to its inherited position in the extended word. -/
@[simp]
theorem moduleMap_app_single {C : Word R}
    (cohook : LeftCohookExtension C) (hmono : IsMonomial R) {x : Q}
    (i : C.PositionAt x) (c : k) :
    (cohook.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single i c) =
      Finsupp.single (cohook.position i) c := by
  exact cohook.toLeftNegativeBoundaryExtension.moduleMap_app_single
    hmono i c

/-- A left cohook witnesses that the original word does not end in a deep. -/
theorem not_endsInDeep {C : Word R}
    (cohook : LeftCohookExtension C) :
    ¬ C.EndsInDeep :=
  cohook.cohook.not_startsInDeep

/-- In a special-biserial presentation, the result of a left cohook is
uniquely determined by its reversed negative boundary arrow. -/
theorem result_eq_of_boundary_eq
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : SpecialBiserialPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (cohook₁ cohook₂ : LeftCohookExtension C)
    (hboundary :
      (⟨cohook₁.cohook.vertex, cohook₁.cohook.arrow⟩ :
        Quiver.Costar C.reverse.target) =
        ⟨cohook₂.cohook.vertex, cohook₂.cohook.arrow⟩) :
    cohook₁.result = cohook₂.result := by
  have hpairs := CohookExtension.eq_of_boundary_eq P
    cohook₁.cohook cohook₂.cohook hboundary
  have hreversed : cohook₁.reverseResult = cohook₂.reverseResult :=
    congrArg Sigma.fst hpairs
  exact congrArg (fun E : Word P.toPresentation.relations ↦ E.reverse)
    hreversed

/-- Maximal left cohooks are in bijection with the valid negative boundary
arrows at the reversed right endpoint. -/
def boundaryEquiv
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations) :
    LeftCohookExtension C ≃ C.reverse.NegativeAppendArrow :=
  (asReverseCohookEquiv C).trans
    (CohookExtension.boundaryEquiv P C.reverse)

end LeftCohookExtension

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
