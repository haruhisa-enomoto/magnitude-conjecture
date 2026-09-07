import MagnitudeConjecture.Algebra.StringWord

/-!
# Subspace transport along signed paths

The Butler--Ringel detecting functors propagate subspaces of a quiver
representation along strings.  Traversing an ordinary arrow takes the image
of a subspace; traversing its formal inverse takes the preimage.  This file
packages that operation for the right-module convention of the bound path
category and proves its elementary path calculus.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The displayed linear map of an ordinary quiver arrow on a raw right
module over the bound path category. -/
def moduleArrowMap
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (a : x ⟶ y) :
    N.obj (Opposite.op (obj R x)) ⟶
      N.obj (Opposite.op (obj R y)) :=
  N.map (BoundQuiver.arrowMap R a).op

/-- The displayed linear map of an ordinary quiver path on a raw right
module over the bound path category. -/
def modulePathMap
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (p : Quiver.Path x y) :
    N.obj (Opposite.op (obj R x)) ⟶
      N.obj (Opposite.op (obj R y)) :=
  N.map (BoundQuiver.pathMap R p).op

@[simp]
theorem modulePathMap_nil
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k) (x : Q) :
    modulePathMap N (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ := by
  unfold modulePathMap BoundQuiver.pathMap
  change N.map
      (((LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map
        (LinearPathCategory.pathHom Quiver.Path.nil)).op) = 𝟙 _
  rw [LinearPathCategory.pathHom_nil,
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map_id,
    op_id, N.map_id]

@[simp]
theorem modulePathMap_toPath
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (a : x ⟶ y) :
    modulePathMap N a.toPath = moduleArrowMap N a :=
  rfl

/-- Path action respects path concatenation in the displayed direction. -/
theorem modulePathMap_comp
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y z : Q} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    modulePathMap N (p.comp q) =
      modulePathMap N p ≫ modulePathMap N q := by
  unfold modulePathMap
  rw [← pathMap_comp, op_comp, Functor.map_comp]

/-- Appending one arrow to a path appends its displayed module action. -/
theorem modulePathMap_cons
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y z : Q} (p : Quiver.Path x y) (a : y ⟶ z) :
    modulePathMap N (p.cons a) =
      modulePathMap N p ≫ moduleArrowMap N a := by
  exact modulePathMap_comp N p a.toPath

/-- Transport a subspace across one signed arrow.  A positive arrow acts by
direct image; a negative arrow acts by preimage under the corresponding
ordinary-arrow map. -/
def signedArrowSubspace
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (e : SignedArrow x y)
    (U : Submodule k (N.obj (Opposite.op (obj R x)))) :
    Submodule k (N.obj (Opposite.op (obj R y))) :=
  match e with
  | Sum.inl a => U.map (moduleArrowMap N a).hom
  | Sum.inr a => U.comap (moduleArrowMap N a).hom

@[simp]
theorem signedArrowSubspace_positive
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (a : x ⟶ y)
    (U : Submodule k (N.obj (Opposite.op (obj R x)))) :
    signedArrowSubspace N (positiveArrow a) U =
      U.map (moduleArrowMap N a).hom :=
  rfl

@[simp]
theorem signedArrowSubspace_negative
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (a : x ⟶ y)
    (U : Submodule k (N.obj (Opposite.op (obj R y)))) :
    signedArrowSubspace N (negativeArrow a) U =
      U.comap (moduleArrowMap N a).hom :=
  rfl

/-- Transport a subspace along a signed path, applying its signed arrows from
left to right. -/
def signedPathSubspace
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k) :
    {x y : Q} → SignedPath x y →
      Submodule k (N.obj (Opposite.op (obj R x))) →
        Submodule k (N.obj (Opposite.op (obj R y)))
  | _, _, Quiver.Path.nil, U => U
  | _, _, Quiver.Path.cons p e, U =>
      signedArrowSubspace N e (signedPathSubspace N p U)

@[simp]
theorem signedPathSubspace_nil
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x : Q} (U : Submodule k (N.obj (Opposite.op (obj R x)))) :
    signedPathSubspace N (Quiver.Path.nil : SignedPath x x) U = U := by
  simp [signedPathSubspace]

@[simp]
theorem signedPathSubspace_cons
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y z : Q} (p : SignedPath x y) (e : SignedArrow y z)
    (U : Submodule k (N.obj (Opposite.op (obj R x)))) :
    signedPathSubspace N (p.cons e) U =
      signedArrowSubspace N e (signedPathSubspace N p U) := by
  simp [signedPathSubspace]

/-- Transport along a one-arrow path is transport across that signed
arrow. -/
@[simp]
theorem signedPathSubspace_toPath
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (e : SignedArrow x y)
    (U : Submodule k (N.obj (Opposite.op (obj R x)))) :
    signedPathSubspace N e.toPath U = signedArrowSubspace N e U := by
  change signedPathSubspace N
      ((Quiver.Path.nil : SignedPath x x).cons e) U = _
  rw [signedPathSubspace_cons, signedPathSubspace_nil]

/-- Signed-arrow transport is monotone in the input subspace. -/
theorem signedArrowSubspace_mono
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (e : SignedArrow x y)
    {U V : Submodule k (N.obj (Opposite.op (obj R x)))}
    (hUV : U ≤ V) :
    signedArrowSubspace N e U ≤ signedArrowSubspace N e V := by
  cases e with
  | inl a => exact Submodule.map_mono hUV
  | inr a => exact Submodule.comap_mono hUV

/-- A module morphism carries signed-arrow transport into the corresponding
transport of the image subspace.  The statement is an inclusion because
preimages along a negative arrow need not commute with a noninvertible module
morphism. -/
theorem signedArrowSubspace_map_le
    {M N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k} (f : M ⟶ N)
    {x y : Q} (e : SignedArrow x y)
    (U : Submodule k (M.obj (Opposite.op (obj R x)))) :
    (signedArrowSubspace M e U).map
        (f.app (Opposite.op (obj R y))).hom ≤
      signedArrowSubspace N e
        (U.map (f.app (Opposite.op (obj R x))).hom) := by
  cases e with
  | inl a =>
      rintro z ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨f.app (Opposite.op (obj R x)) v, ⟨v, hv, rfl⟩, ?_⟩
      have hnat := f.naturality (BoundQuiver.arrowMap R a).op
      have hnatApply := congrArg (fun g ↦ g.hom v) hnat
      simpa only [moduleArrowMap, ModuleCat.comp_apply] using hnatApply.symm
  | inr a =>
      rintro z ⟨v, hv, rfl⟩
      change
        moduleArrowMap N a (f.app (Opposite.op (obj R y)) v) ∈
          U.map (f.app (Opposite.op (obj R x))).hom
      refine ⟨moduleArrowMap M a v, hv, ?_⟩
      have hnat := f.naturality (BoundQuiver.arrowMap R a).op
      have hnatApply := congrArg (fun g ↦ g.hom v) hnat
      simpa only [moduleArrowMap, ModuleCat.comp_apply] using hnatApply

/-- Signed-path transport is monotone in the input subspace. -/
theorem signedPathSubspace_mono
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k) :
    ∀ {x y : Q} (p : SignedPath x y)
      {U V : Submodule k (N.obj (Opposite.op (obj R x)))},
      U ≤ V → signedPathSubspace N p U ≤ signedPathSubspace N p V := by
  intro x y p
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
      cases p with
      | nil =>
          intro U V hUV
          simpa only [signedPathSubspace_nil] using hUV
      | @cons y z p e =>
          change Q at y
          intro U V hUV
          rw [signedPathSubspace_cons, signedPathSubspace_cons]
          apply signedArrowSubspace_mono N e
          apply ih p.length
          · simp only [Quiver.Path.length_cons] at hlength
            omega
          · rfl
          · exact hUV

/-- A module morphism carries signed-path transport into the transport of the
image subspace. -/
theorem signedPathSubspace_map_le
    {M N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k} (f : M ⟶ N) :
    ∀ {x y : Q} (p : SignedPath x y)
      (U : Submodule k (M.obj (Opposite.op (obj R x)))),
      (signedPathSubspace M p U).map
          (f.app (Opposite.op (obj R y))).hom ≤
        signedPathSubspace N p
          (U.map (f.app (Opposite.op (obj R x))).hom) := by
  intro x y p
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
      cases p with
      | nil =>
          intro U
          simp only [signedPathSubspace_nil]
          exact le_rfl
      | @cons y z p e =>
          change Q at y
          intro U
          rw [signedPathSubspace_cons, signedPathSubspace_cons]
          exact (signedArrowSubspace_map_le f e
            (signedPathSubspace M p U)).trans
              (signedArrowSubspace_mono N e (by
                apply ih p.length
                · simp only [Quiver.Path.length_cons] at hlength
                  omega
                · rfl))

/-- Transport along a composite signed path is iterated transport. -/
theorem signedPathSubspace_comp
    (N : (Category R)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y z : Q} (p : SignedPath x y) (q : SignedPath y z)
    (U : Submodule k (N.obj (Opposite.op (obj R x)))) :
    signedPathSubspace N (p.comp q) U =
      signedPathSubspace N q (signedPathSubspace N p U) := by
  induction hlength : q.length using Nat.strong_induction_on generalizing y z with
  | h n ih =>
      cases q with
      | nil => simp
      | @cons y z q e =>
          change Q at y
          rw [Quiver.Path.comp_cons, signedPathSubspace_cons,
            signedPathSubspace_cons]
          apply congrArg (signedArrowSubspace N e)
          apply ih q.length
          · simp only [Quiver.Path.length_cons] at hlength
            omega
          · rfl

end MagnitudeConjecture.BoundQuiver.StringWord
