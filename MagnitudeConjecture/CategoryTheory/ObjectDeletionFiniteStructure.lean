import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleInheritance
import MagnitudeConjecture.CategoryTheory.OrbitPushdownCorepresentable

/-!
# Finite structural data inherited by object deletion

The finite-cover push-down theorem needs finite representables, finite dual
corepresentables, and local vertex endomorphism rings at every intermediate
deletion stage.  These properties descend from the ambient locally bounded
skeletal category.  Hom spaces downstairs are quotients of ambient Hom
spaces, while the deletion ideal at a surviving object lies in its categorical
radical and hence cannot kill the identity.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

private theorem deletionObjectUnderlying_injective (S : Set C) :
    Function.Injective
      (fun X : DeletionCategory (k := k) C S ↦ X.obj.as) := by
  intro X Y hXY
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Quotient.ext
  exact hXY

private theorem deletionFunctor_obj_surviving_eq (S : Set C)
    (X : DeletionCategory (k := k) C S) :
    (functor (k := k) C S).obj
        (show SurvivingCategory C S from ⟨X.obj.as, X.property⟩) = X := by
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Quotient.ext
  rfl

/-- Finite-dimensionality and finite support of covariant representables
pass to an object-deletion quotient. -/
theorem deletion_linearCoyoneda_isFiniteDimensional
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (S : Set C) (X : DeletionCategory (k := k) C S) :
    IsFiniteDimensionalModule
      (C := DeletionCategory (k := k) C S) k
      (linearCoyonedaLinearModule (k := k) X) := by
  let F := functor (k := k) C S
  let X₀ : SurvivingCategory C S := ⟨X.obj.as, X.property⟩
  constructor
  · intro Y
    let Y₀ : SurvivingCategory C S := ⟨Y.obj.as, Y.property⟩
    let J := (IsSurviving C S).ι
    let eX : F.obj X₀ ≅ X := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S X)
    let eY : F.obj Y₀ ≅ Y := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S Y)
    let p := (CategoryTheory.Linear.homCongr k eX eY).toLinearMap.comp
      (F.mapLinearMap k (X := X₀) (Y := Y₀))
    have hp : Function.Surjective p :=
      (CategoryTheory.Linear.homCongr k eX eY).surjective.comp
        F.map_surjective
    have hambient := (hP X.obj.as).1 Y.obj.as
    change FiniteDimensional k (X.obj.as ⟶ Y.obj.as) at hambient
    letI : FiniteDimensional k (X.obj.as ⟶ Y.obj.as) := hambient
    letI : FiniteDimensional k (X₀ ⟶ Y₀) := by
      letI : FiniteDimensional k (J.obj X₀ ⟶ J.obj Y₀) := by
        change FiniteDimensional k (X.obj.as ⟶ Y.obj.as)
        infer_instance
      exact FiniteDimensional.of_injective
        (J.mapLinearMap k (X := X₀) (Y := Y₀)) J.map_injective
    change FiniteDimensional k (X ⟶ Y)
    exact FiniteDimensional.of_surjective p hp
  · refine ((hP X.obj.as).2.preimage
      (deletionObjectUnderlying_injective (k := k) C S).injOn).subset ?_
    intro Y hY
    change Nontrivial (X ⟶ Y) at hY
    change Nontrivial (X.obj.as ⟶ Y.obj.as)
    let Y₀ : SurvivingCategory C S := ⟨Y.obj.as, Y.property⟩
    let J := (IsSurviving C S).ι
    let eX : F.obj X₀ ≅ X := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S X)
    let eY : F.obj Y₀ ≅ Y := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S Y)
    let p := (CategoryTheory.Linear.homCongr k eX eY).toLinearMap.comp
      (F.mapLinearMap k (X := X₀) (Y := Y₀))
    have hp : Function.Surjective p :=
      (CategoryTheory.Linear.homCongr k eX eY).surjective.comp
        F.map_surjective
    letI : Nontrivial (X ⟶ Y) := hY
    letI : Nontrivial (X₀ ⟶ Y₀) := hp.nontrivial
    have hamb :=
      (show Function.Injective
          (J.map : (X₀ ⟶ Y₀) → (J.obj X₀ ⟶ J.obj Y₀)) from
        J.map_injective).nontrivial
    change Nontrivial (X.obj.as ⟶ Y.obj.as) at hamb
    exact hamb

/-- Finite-dimensionality and finite support of coefficient-dual
corepresentables pass to an object-deletion quotient. -/
theorem deletion_dualLinearYoneda_isFiniteDimensional
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (S : Set C) (X : DeletionCategory (k := k) C S) :
    IsFiniteDimensionalModule
      (C := DeletionCategory (k := k) C S) k
      (dualLinearYonedaLinearModule (k := k) X) := by
  let F := functor (k := k) C S
  let X₀ : SurvivingCategory C S := ⟨X.obj.as, X.property⟩
  constructor
  · intro Y
    let Y₀ : SurvivingCategory C S := ⟨Y.obj.as, Y.property⟩
    let J := (IsSurviving C S).ι
    let eY : F.obj Y₀ ≅ Y := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S Y)
    let eX : F.obj X₀ ≅ X := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S X)
    let p := (CategoryTheory.Linear.homCongr k eY eX).toLinearMap.comp
      (F.mapLinearMap k (X := Y₀) (Y := X₀))
    have hp : Function.Surjective p :=
      (CategoryTheory.Linear.homCongr k eY eX).surjective.comp
        F.map_surjective
    have hpdual : Function.Injective p.dualMap := by
      intro φ ψ hφψ
      apply LinearMap.ext
      intro q
      obtain ⟨r, rfl⟩ := hp q
      exact LinearMap.congr_fun hφψ r
    let j := J.mapLinearMap k (X := Y₀) (Y := X₀)
    have hj : Function.Injective j := J.map_injective
    have hambient := (hI X.obj.as).1 Y.obj.as
    change FiniteDimensional k
      (Module.Dual k (Y.obj.as ⟶ X.obj.as)) at hambient
    letI : FiniteDimensional k
        (Module.Dual k (Y.obj.as ⟶ X.obj.as)) := hambient
    letI : FiniteDimensional k
        (Module.Dual k (J.obj Y₀ ⟶ J.obj X₀)) := by
      change FiniteDimensional k
        (Module.Dual k (Y.obj.as ⟶ X.obj.as))
      infer_instance
    letI : FiniteDimensional k (Module.Dual k (Y₀ ⟶ X₀)) :=
      FiniteDimensional.of_surjective j.dualMap
        (LinearMap.dualMap_surjective_of_injective hj)
    change FiniteDimensional k (Module.Dual k (Y ⟶ X))
    exact FiniteDimensional.of_injective p.dualMap hpdual
  · refine ((hI X.obj.as).2.preimage
      (deletionObjectUnderlying_injective (k := k) C S).injOn).subset ?_
    intro Y hY
    change Nontrivial (Module.Dual k (Y ⟶ X)) at hY
    change Nontrivial (Module.Dual k (Y.obj.as ⟶ X.obj.as))
    let Y₀ : SurvivingCategory C S := ⟨Y.obj.as, Y.property⟩
    let J := (IsSurviving C S).ι
    let eY : F.obj Y₀ ≅ Y := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S Y)
    let eX : F.obj X₀ ≅ X := eqToIso
      (deletionFunctor_obj_surviving_eq (k := k) C S X)
    let p := (CategoryTheory.Linear.homCongr k eY eX).toLinearMap.comp
      (F.mapLinearMap k (X := Y₀) (Y := X₀))
    have hp : Function.Surjective p :=
      (CategoryTheory.Linear.homCongr k eY eX).surjective.comp
        F.map_surjective
    have hpdual : Function.Injective p.dualMap := by
      intro φ ψ hφψ
      apply LinearMap.ext
      intro q
      obtain ⟨r, rfl⟩ := hp q
      exact LinearMap.congr_fun hφψ r
    letI : Nontrivial (Module.Dual k (Y ⟶ X)) := hY
    letI : Nontrivial (Module.Dual k (Y₀ ⟶ X₀)) :=
      hpdual.nontrivial
    let j := J.mapLinearMap k (X := Y₀) (Y := X₀)
    have hamb : Nontrivial (Module.Dual k (J.obj Y₀ ⟶ J.obj X₀)) :=
      (LinearMap.dualMap_surjective_of_injective
        (show Function.Injective j from J.map_injective)).nontrivial
    change Nontrivial
      (Module.Dual k (Y.obj.as ⟶ X.obj.as)) at hamb
    exact hamb

private theorem not_isZero_of_localEnd
    {X : C} [IsLocalRing (End X)] : ¬ IsZero X := by
  intro hX
  have h : (1 : End X) = 0 := by
    change (𝟙 X : X ⟶ X) = 0
    exact (IsZero.iff_id_eq_zero X).mp hX
  exact one_ne_zero h

private theorem isIso_of_isSplitMono_toLocalEnd
    {X Y : C} [IsLocalRing (End Y)]
    (f : X ⟶ Y) [IsSplitMono f] (hX : ¬ IsZero X) : IsIso f := by
  let r : Y ⟶ X := retraction f
  let p : End Y := End.of (r ≫ f)
  have hp : IsIdempotentElem p := by
    change p * p = p
    apply End.ext
    change (r ≫ f) ≫ r ≫ f = r ≫ f
    dsimp only [r]
    rw [← Category.assoc (retraction f ≫ f) (retraction f) f,
      Category.assoc (retraction f) f (retraction f),
      IsSplitMono.id, Category.comp_id]
  rcases
      QuotientSubmoduleEquidistribution.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
        hp with hpzero | hpone
  · exfalso
    apply hX
    apply (IsZero.iff_id_eq_zero X).mpr
    have hrf : r ≫ f = 0 := hpzero
    have hf : f = 0 := by
      calc
        f = (f ≫ r) ≫ f := by rw [IsSplitMono.id, Category.id_comp]
        _ = f ≫ (r ≫ f) := Category.assoc _ _ _
        _ = 0 := by rw [hrf, comp_zero]
    calc
      𝟙 X = f ≫ r := (IsSplitMono.id f).symm
      _ = 0 := by rw [hf, zero_comp]
  · apply IsIso.mk
    exact ⟨r, IsSplitMono.id f, hpone⟩

/-- At a surviving object, every endomorphism in the deletion ideal is
radical.  Each spanning term factors through a deleted object, which cannot
be isomorphic to the surviving source in a skeletal category. -/
theorem deletionIdeal_end_isRadical
    (hC : Skeletal C) (hlocal : ∀ X : C, IsLocalRing (End X))
    (S : Set C) (X : C) (hX : X ∉ S) {f : X ⟶ X}
    (hf : f ∈ (ideal (k := k) C S).hom X X) :
    IsRadicalMorphism f := by
  change f ∈ HomIdeal.generatedHomSubmodule k
    (endomorphismRelations C S) X X at hf
  have hrad : f ∈
      (QuotientSubmoduleEquidistribution.CategoricalRadical.homIdeal :
        HomIdeal C).hom X X := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with ⟨A, B, r, hr, a, b, rfl⟩
        rcases hr with ⟨hAB, hA⟩
        subst B
        letI : IsLocalRing (End X) := hlocal X
        letI : IsLocalRing (End A) := hlocal A
        have hXA : ¬ Nonempty (X ≅ A) := by
          rintro ⟨e⟩
          apply hX
          exact (hC ⟨e⟩).symm ▸ hA
        have ha : IsRadicalMorphism a := by
          apply (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
            (not_isZero_of_localEnd C) a).2
          intro haSplit
          letI : IsSplitMono a := haSplit
          haveI : IsIso a :=
            isIso_of_isSplitMono_toLocalEnd C a
              (not_isZero_of_localEnd C)
          exact hXA ⟨asIso a⟩
        exact
          (QuotientSubmoduleEquidistribution.CategoricalRadical.homIdeal :
            HomIdeal C).postcomp (r ≫ b) ha
    | zero =>
        exact (QuotientSubmoduleEquidistribution.CategoricalRadical.homIdeal :
          HomIdeal C).hom X X |>.zero_mem
    | add f g _ _ hf hg =>
        exact (QuotientSubmoduleEquidistribution.CategoricalRadical.homIdeal :
          HomIdeal C).hom X X |>.add_mem hf hg
    | smul c f _ hf =>
        exact
          (QuotientSubmoduleEquidistribution.CategoricalRadical.homIdeal :
            HomIdeal C).smul_mem c hf
  exact hrad

set_option backward.isDefEq.respectTransparency false in
/-- Deleting objects from a skeletal category with local endomorphism rings
does not identify two surviving objects up to isomorphism. -/
theorem deletion_skeletal
    (hC : Skeletal C) (hlocal : ∀ X : C, IsLocalRing (End X))
    (S : Set C) : Skeletal (DeletionCategory (k := k) C S) := by
  intro X Y hXY
  rcases hXY with ⟨e⟩
  rcases X with ⟨⟨X⟩, hX⟩
  rcases Y with ⟨⟨Y⟩, hY⟩
  obtain ⟨f, hf⟩ := (rawFunctor (k := k) C S).map_surjective e.hom.hom
  obtain ⟨g, hg⟩ := (rawFunctor (k := k) C S).map_surjective e.inv.hom
  have hfgZero : (rawFunctor (k := k) C S).map
      (f ≫ g - 𝟙 X) = 0 := by
    rw [(rawFunctor (k := k) C S).map_sub,
      (rawFunctor (k := k) C S).map_comp, hf, hg]
    have he : e.hom.hom ≫ e.inv.hom = 𝟙 ((rawFunctor (k := k) C S).obj X) :=
      congrArg (fun q ↦ q.hom) e.hom_inv_id
    rw [he]
    exact sub_eq_zero.mpr ((rawFunctor (k := k) C S).map_id X).symm
  have hgfZero : (rawFunctor (k := k) C S).map
      (g ≫ f - 𝟙 Y) = 0 := by
    rw [(rawFunctor (k := k) C S).map_sub,
      (rawFunctor (k := k) C S).map_comp, hg, hf]
    have he : e.inv.hom ≫ e.hom.hom = 𝟙 ((rawFunctor (k := k) C S).obj Y) :=
      congrArg (fun q ↦ q.hom) e.inv_hom_id
    rw [he]
    exact sub_eq_zero.mpr ((rawFunctor (k := k) C S).map_id Y).symm
  have hfgRad : IsRadicalMorphism (f ≫ g - 𝟙 X) :=
    deletionIdeal_end_isRadical (k := k) C hC hlocal S X
      hX (((ideal (k := k) C S).map_eq_zero_iff _).1 hfgZero)
  have hgfRad : IsRadicalMorphism (g ≫ f - 𝟙 Y) :=
    deletionIdeal_end_isRadical (k := k) C hC hlocal S Y
      hY (((ideal (k := k) C S).map_eq_zero_iff _).1 hgfZero)
  haveI : IsIso (f ≫ g) := by
    have hi := hfgRad (-𝟙 X)
    simpa using hi
  haveI : IsIso (g ≫ f) := by
    have hi := hgfRad (-𝟙 Y)
    simpa using hi
  haveI : IsIso f := by
    let r : Y ⟶ X := g ≫ inv (f ≫ g)
    let l : Y ⟶ X := inv (g ≫ f) ≫ g
    have hr : f ≫ r = 𝟙 X := by
      dsimp only [r]
      rw [← Category.assoc, IsIso.hom_inv_id]
    have hl : l ≫ f = 𝟙 Y := by
      dsimp only [l]
      rw [Category.assoc, IsIso.inv_hom_id]
    have hrl : r = l := by
      calc
        r = 𝟙 Y ≫ r := by simp
        _ = (l ≫ f) ≫ r := by rw [hl]
        _ = l ≫ (f ≫ r) := Category.assoc _ _ _
        _ = l ≫ 𝟙 X := by rw [hr]
        _ = l := by simp
    exact ⟨⟨r, hr, hrl ▸ hl⟩⟩
  have hUnderlying : X = Y := hC ⟨asIso f⟩
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Quotient.ext
  exact hUnderlying

private theorem deletion_id_not_mem_ideal
    (hC : Skeletal C) (hlocal : ∀ X : C, IsLocalRing (End X))
    (S : Set C) (X : C) (hX : X ∉ S) :
    𝟙 X ∉ (ideal (k := k) C S).hom X X := by
  intro hid
  letI : IsLocalRing (End X) := hlocal X
  have hr : IsRadicalMorphism (𝟙 X) :=
    deletionIdeal_end_isRadical (k := k) C hC hlocal S X hX hid
  haveI : IsIso (0 : X ⟶ X) := by
    simpa using hr (𝟙 X)
  exact not_isZero_of_localEnd C
    ((IsZero.iff_isSplitEpi_eq_zero (0 : X ⟶ X)).2 rfl)

/-- Local endomorphism rings descend to every surviving vertex of an
object-deletion quotient of a skeletal category. -/
theorem deletion_end_isLocalRing
    (hC : Skeletal C) (hlocal : ∀ X : C, IsLocalRing (End X))
    (S : Set C) (X : DeletionCategory (k := k) C S) :
    IsLocalRing (End X) := by
  let F := functor (k := k) C S
  let J := (IsSurviving C S).ι
  let X₀ : SurvivingCategory C S := ⟨X.obj.as, X.property⟩
  let eX : F.obj X₀ ≅ X := eqToIso
    (deletionFunctor_obj_surviving_eq (k := k) C S X)
  letI : IsLocalRing (End (J.obj X₀)) := by
    change IsLocalRing (End X.obj.as)
    exact hlocal X.obj.as
  letI : IsLocalRing (End X₀) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (MagnitudeConjecture.CategoryTheory.Functor.endRingEquivOfFullyFaithful
        J X₀).symm
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
    intro hid
    have hzeroX : IsZero X := (IsZero.iff_id_eq_zero X).2 hid
    have hzeroFX : IsZero (F.obj X₀) := eX.isZero_iff.mpr hzeroX
    have hmap : F.map (𝟙 X₀) = 0 := hzeroFX.eq_of_src _ _
    have hideal := (functor_map_eq_zero_iff (k := k) C S (𝟙 X₀)).1 hmap
    change 𝟙 X.obj.as ∈ (ideal (k := k) C S).hom X.obj.as X.obj.as at hideal
    exact deletion_id_not_mem_ideal (k := k) C hC hlocal S
      X.obj.as X.property hideal
  letI : Nontrivial (End X) := ⟨⟨𝟙 X, 0, hid⟩⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro q
  let p := (CategoryTheory.Linear.homCongr k eX eX).toLinearMap.comp
    (F.mapLinearMap k (X := X₀) (Y := X₀))
  have hp : Function.Surjective p :=
    (CategoryTheory.Linear.homCongr k eX eX).surjective.comp
      F.map_surjective
  obtain ⟨f, rfl⟩ := hp q
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := End X₀) (a := End.of f) (b := 1 - End.of f)
      (add_sub_cancel (End.of f) 1) with hf | hf
  · left
    haveI : IsIso f := (isUnit_iff_isIso f).1 hf
    apply (isUnit_iff_isIso (p f)).2
    have hpf : p f = eX.inv ≫ F.map f ≫ eX.hom := by
      dsimp only [p, LinearMap.comp_apply]
      change (eX.inv ≫ F.map f) ≫ eX.hom = _
      exact Category.assoc _ _ _
    rw [hpf]
    infer_instance
  · right
    haveI : IsIso (𝟙 X₀ - f) :=
      (isUnit_iff_isIso (𝟙 X₀ - f)).1 hf
    have hunit : IsUnit (End.of (p (𝟙 X₀ - f))) := by
      apply (isUnit_iff_isIso (p (𝟙 X₀ - f))).2
      have hpf : p (𝟙 X₀ - f) =
          eX.inv ≫ F.map (𝟙 X₀ - f) ≫ eX.hom := by
        dsimp only [p, LinearMap.comp_apply]
        change (eX.inv ≫ F.map (𝟙 X₀ - f)) ≫ eX.hom = _
        exact Category.assoc _ _ _
      rw [hpf]
      infer_instance
    have hp_id : p (𝟙 X₀) = 𝟙 X := by
      dsimp only [p]
      simp [CategoryTheory.Linear.homCongr_apply]
    have hp_sub : p (𝟙 X₀ - f) = 𝟙 X - p f := by
      rw [map_sub, hp_id]
    rw [hp_sub] at hunit
    exact hunit

end MagnitudeConjecture.ObjectDeletion
