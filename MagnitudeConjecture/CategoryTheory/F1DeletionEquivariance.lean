import MagnitudeConjecture.CategoryTheory.F1FiniteSupportEquivariance

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.ObjectDeletion

universe u v w
variable {k : Type w} [Ring k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

section
universe u₂ v₂
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]

/-- The deleted-object set transported along an equivalence.

This is the inverse image of the source set, so an object of `D` is deleted
exactly when its chosen inverse image in `C` is deleted. -/
def equivalenceDeletedSet (e : C ≌ D) (S : Set C) : Set D :=
  fun Y ↦ e.inverse.obj Y ∈ S

noncomputable instance equivalenceDeletedSet_isClosedUnderIsomorphisms
    (e : C ≌ D) (S : Set C)
    [ObjectProperty.IsClosedUnderIsomorphisms S] :
    ObjectProperty.IsClosedUnderIsomorphisms (equivalenceDeletedSet e S) := by
  constructor
  intro X Y i hX
  change e.inverse.obj Y ∈ S
  exact ObjectProperty.prop_of_iso S (e.inverse.mapIso i) hX

 theorem map_mem_ideal
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ (ideal (k := k) C S).hom X Y) :
    e.functor.map f ∈
      (ideal (k := k) D (equivalenceDeletedSet e S)).hom
        (e.functor.obj X) (e.functor.obj Y) := by
  change f ∈ HomIdeal.generatedHomSubmodule k
    (endomorphismRelations C S) X Y at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨A, B, r, ⟨rfl, hA⟩, a, b, rfl⟩
      rw [e.functor.map_comp, e.functor.map_comp]
      have hA' : e.inverse.obj (e.functor.obj A) ∈ S :=
        ObjectProperty.prop_of_iso S (e.unitIso.app A) hA
      exact comp_mem_ideal (k := k) D (equivalenceDeletedSet e S) hA' _ _
  | zero =>
      rw [e.functor.map_zero]
      exact (ideal (k := k) D (equivalenceDeletedSet e S)).hom
        (e.functor.obj X) (e.functor.obj Y) |>.zero_mem
  | add g h _ _ hg hh =>
      rw [e.functor.map_add]
      exact (ideal (k := k) D (equivalenceDeletedSet e S)).hom
        (e.functor.obj X) (e.functor.obj Y) |>.add_mem hg hh
  | smul r g _ hg =>
      rw [e.functor.map_smul]
      exact HomIdeal.smul_mem
        (ideal (k := k) D (equivalenceDeletedSet e S)) r hg

 theorem mem_ideal_of_map
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    {X Y : C} {f : X ⟶ Y}
    (hf : e.functor.map f ∈
      (ideal (k := k) D (equivalenceDeletedSet e S)).hom
        (e.functor.obj X) (e.functor.obj Y)) :
    f ∈ (ideal (k := k) C S).hom X Y := by
  change e.functor.map f ∈
    HomIdeal.generatedHomSubmodule k
      (endomorphismRelations D (equivalenceDeletedSet e S))
      (e.functor.obj X) (e.functor.obj Y) at hf
  have hpre (g : e.functor.obj X ⟶ e.functor.obj Y)
      (hg : g ∈ HomIdeal.generatedHomSubmodule k
        (endomorphismRelations D (equivalenceDeletedSet e S))
        (e.functor.obj X) (e.functor.obj Y)) :
      e.inverse.map g ∈
        (ideal (k := k) C S).hom (e.inverse.obj (e.functor.obj X))
          (e.inverse.obj (e.functor.obj Y)) := by
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨A, B, r, ⟨rfl, hA⟩, a, b, rfl⟩
        have hA' : e.inverse.obj A ∈ S := hA
        rw [e.inverse.map_comp, e.inverse.map_comp]
        exact comp_mem_ideal (k := k) C S hA'
          (e.inverse.map a)
          (e.inverse.map r ≫ e.inverse.map b)
    | zero =>
        rw [e.inverse.map_zero]
        exact (ideal (k := k) C S).hom
          (e.inverse.obj (e.functor.obj X))
          (e.inverse.obj (e.functor.obj Y)) |>.zero_mem
    | add g h _ _ hg hh =>
        rw [e.inverse.map_add]
        exact (ideal (k := k) C S).hom
          (e.inverse.obj (e.functor.obj X))
          (e.inverse.obj (e.functor.obj Y)) |>.add_mem hg hh
    | smul r g _ hg =>
        rw [e.inverse.map_smul]
        exact HomIdeal.smul_mem (ideal (k := k) C S) r hg
  have h := hpre (e.functor.map f) hf
  have h' := (ideal (k := k) C S).precomp (e.unitIso.hom.app X) h
  have h'' := (ideal (k := k) C S).postcomp (e.unitIso.inv.app Y) h'
  simpa using h''

 theorem imageIdeal_isKilledBy
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    (ideal (k := k) C S).IsKilledBy
      (e.functor ⋙ rawFunctor (k := k) D (equivalenceDeletedSet e S)) := by
  intro X Y f hf
  exact ((ideal (k := k) D (equivalenceDeletedSet e S)).map_eq_zero_iff
    (e.functor.map f)).2
      (map_mem_ideal (k := k) e S hf)

def rawDeletionMapFunctor
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    RawCategory (k := k) C S ⥤
      RawCategory (k := k) D (equivalenceDeletedSet e S) :=
  (ideal (k := k) C S).quotientLift
    (e.functor ⋙ rawFunctor (k := k) D (equivalenceDeletedSet e S))
    (imageIdeal_isKilledBy (k := k) e S)

noncomputable instance rawDeletionMapFunctor_additive
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] : (rawDeletionMapFunctor (k := k) e S).Additive := by
  unfold rawDeletionMapFunctor
  infer_instance

noncomputable instance rawDeletionMapFunctor_linear
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] : (rawDeletionMapFunctor (k := k) e S).Linear k := by
  unfold rawDeletionMapFunctor
  infer_instance

noncomputable instance rawDeletionMapFunctor_full
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] : (rawDeletionMapFunctor (k := k) e S).Full := by
  unfold rawDeletionMapFunctor
  infer_instance

noncomputable instance rawDeletionMapFunctor_faithful
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] : (rawDeletionMapFunctor (k := k) e S).Faithful := by
  apply HomIdeal.quotientLift_faithful
  intro X Y f hf
  apply mem_ideal_of_map (k := k) e S
  exact ((ideal (k := k) D (equivalenceDeletedSet e S)).map_eq_zero_iff
    (e.functor.map f)).1 hf

def deletionMapFunctor
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    DeletionCategory (k := k) C S ⥤
      DeletionCategory (k := k) D (equivalenceDeletedSet e S) where
  obj X := ⟨(rawDeletionMapFunctor (k := k) e S).obj X.obj, by
    intro hdel
    have hdel' : e.inverse.obj (e.functor.obj X.obj.as) ∈ S := by
      change e.inverse.obj (e.functor.obj X.obj.as) ∈ S at hdel
      exact hdel
    exact X.property (ObjectProperty.prop_of_iso S
      (e.unitIso.app X.obj.as).symm hdel')⟩
  map f := ObjectProperty.homMk
    ((rawDeletionMapFunctor (k := k) e S).map f.hom)

end
end MagnitudeConjecture.ObjectDeletion

namespace MagnitudeConjecture.ObjectDeletion

universe u v w
variable {k : Type w} [Ring k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
universe u₂ v₂
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]

noncomputable instance deletionMapFunctor_additive
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    (deletionMapFunctor (k := k) e S).Additive := by
  constructor
  intro X Y f g
  apply ObjectProperty.hom_ext
  exact (rawDeletionMapFunctor (k := k) e S).map_add

noncomputable instance deletionMapFunctor_linear
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    (deletionMapFunctor (k := k) e S).Linear k := by
  constructor
  intro X Y f r
  apply ObjectProperty.hom_ext
  exact (rawDeletionMapFunctor (k := k) e S).map_smul r f.hom

noncomputable instance deletionMapFunctor_full
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    (deletionMapFunctor (k := k) e S).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ :=
      (rawDeletionMapFunctor (k := k) e S).map_surjective f.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

noncomputable instance deletionMapFunctor_faithful
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    (deletionMapFunctor (k := k) e S).Faithful where
  map_injective {X Y} f g hfg := by
    apply ObjectProperty.hom_ext
    apply (rawDeletionMapFunctor (k := k) e S).map_injective
    exact congrArg (fun h ↦ h.hom) hfg

noncomputable instance deletionMapFunctor_essSurj
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    (deletionMapFunctor (k := k) e S).EssSurj where
  mem_essImage Y := by
    let X₀ := e.inverse.obj Y.obj.as
    have hX₀ : X₀ ∉ S := by
      intro hS
      have hmap : Y.obj.as ∈ equivalenceDeletedSet e S := hS
      exact Y.property hmap
    let X : DeletionCategory (k := k) C S :=
      ⟨(rawFunctor (k := k) C S).obj X₀, hX₀⟩
    refine ⟨X, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact (rawFunctor (k := k) D (equivalenceDeletedSet e S)).mapIso
      (e.counitIso.app Y.obj.as)

noncomputable def deletionEquivalence
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S] :
    DeletionCategory (k := k) C S ≌
      DeletionCategory (k := k) D (equivalenceDeletedSet e S) := by
  letI : (deletionMapFunctor (k := k) e S).EssSurj :=
    deletionMapFunctor_essSurj (k := k) e S
  letI : (deletionMapFunctor (k := k) e S).IsEquivalence := {}
  exact (deletionMapFunctor (k := k) e S).asEquivalence

end MagnitudeConjecture.ObjectDeletion
