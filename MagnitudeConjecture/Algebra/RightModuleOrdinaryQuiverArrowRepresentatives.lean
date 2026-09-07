import MagnitudeConjecture.Algebra.BoundQuiverPresentation
import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiver
import MagnitudeConjecture.CategoryTheory.LinearIdealQuotientLift
import MagnitudeConjecture.CategoryTheory.LinearPathKernelFiltration
import MagnitudeConjecture.CategoryTheory.RadicalMinimality

/-!
# Representatives of ordinary-quiver arrows

The ordinary quiver remembers only a basis of each projective radical quotient
`rad / rad²`.  A bound-quiver realization additionally chooses a radical
representative of every basis vector.  Skowroński--Waschbüsch's
special-biserial construction changes these representatives, so the choice is
made explicit here rather than identified with the ordinary quiver itself.

Any two choices differ in the internal projective radical square.  More
generally, their evaluations of a path of length `n` agree modulo the
`(n + 1)`-st radical power.  Thus changing representatives is unitriangular
for the projective-radical filtration, although literal zero/nonzero
two-arrow compositions need not be preserved.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

/-- A simultaneous choice of radical representatives for the fixed basis
arrows of the ordinary projective quiver. -/
structure OrdinaryArrowRepresentatives where
  representative :
    ∀ {x y : S.ProjectiveLabel}, S.OrdinaryArrow x y →
      S.projectiveRadicalSubmodule x y
  representative_mkQ :
    ∀ {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y),
      Submodule.Quotient.mk (representative a) =
        S.ordinaryArrowClass a

namespace OrdinaryArrowRepresentatives

/-- The selected-projective morphism represented by an ordinary arrow. -/
def hom (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x :=
  (D.representative a).1

theorem hom_mem_radical (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    D.hom a ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) :=
  (D.representative a).2

/-- A representative of a displayed ordinary arrow does not lie in the
internal projective radical square. -/
theorem hom_not_mem_radicalSquare (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    D.hom a ∉ S.projectiveRadicalSquareSubmodule x y := by
  intro ha
  have ha' : D.representative a ∈
      S.projectiveRadicalSquareInRadicalSubmodule x y :=
    ha
  have hzero :
      (S.projectiveRadicalSquareInRadicalSubmodule x y).mkQ
        (D.representative a) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ha'
  change Submodule.Quotient.mk (D.representative a) = 0 at hzero
  rw [D.representative_mkQ] at hzero
  exact (S.ordinaryArrowBasis x y).ne_zero a hzero

/-- If postcomposition carries an ordinary-arrow representative into the
internal projective radical square, the endomorphism multiplier is radical.
The local-ring argument is performed in the ambient right-module category;
full faithfulness then reflects the resulting split mono for cancellation. -/
theorem codomainEndomorphism_mem_radical_of_comp_mem_radicalSquare
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y)
    (e : S.ordinaryProjectiveObj x ⟶ S.ordinaryProjectiveObj x)
    (hcomp : D.hom a ≫ e ∈ S.projectiveRadicalSquareSubmodule x y) :
    e ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj x) (S.ordinaryProjectiveObj x) := by
  by_contra he
  have heAmbient :
      ¬ CategoricalRadical.IsRadicalMorphism
        (S.projectiveInclusion.map e) := by
    intro heRad
    apply he
    rw [S.projectiveNilpotentRadicalData.mem_ideal_iff]
    exact (isRadicalMorphism_iff_map_of_fullyFaithful
      S.projectiveInclusion
      (CategoryTheory.fullyFaithfulInducedFunctor _) e).2 heRad
  letI : IsLocalRing (End (S.fgObj x.label)) :=
    S.fgObj_end_isLocalRing x.label
  have heSplitAmbient : IsSplitMono (S.projectiveInclusion.map e) := by
    by_contra hsplit
    exact heAmbient
      ((MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
        (S.fgObj_indecomposable x.label).1 _).2 hsplit)
  letI : IsSplitMono (S.projectiveInclusion.map e) := heSplitAmbient
  letI : S.projectiveInclusion.Full :=
    (CategoryTheory.fullyFaithfulInducedFunctor _).full
  letI : S.projectiveInclusion.Faithful :=
    (CategoryTheory.fullyFaithfulInducedFunctor _).faithful
  have heSplit : IsSplitMono e := by
    apply IsSplitMono.mk'
    refine ⟨S.projectiveInclusion.preimage
      (retraction (S.projectiveInclusion.map e)), ?_⟩
    apply S.projectiveInclusion.map_injective
    rw [S.projectiveInclusion.map_comp,
      S.projectiveInclusion.map_preimage,
      IsSplitMono.id]
    exact (S.projectiveInclusion.map_id _).symm
  letI : IsSplitMono e := heSplit
  apply D.hom_not_mem_radicalSquare a
  have hcancel :=
    (S.projectiveNilpotentRadicalData.ideal.pow 2).postcomp
      (retraction e) hcomp
  change D.hom a ∈
    (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _
  simpa only [Category.assoc, IsSplitMono.id, Category.comp_id] using hcancel

/-- If precomposition carries an ordinary-arrow representative into the
internal projective radical square, the endomorphism multiplier is radical.
This is the split-epi dual of
`codomainEndomorphism_mem_radical_of_comp_mem_radicalSquare`. -/
theorem domainEndomorphism_mem_radical_of_comp_mem_radicalSquare
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y)
    (e : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj y)
    (hcomp : e ≫ D.hom a ∈ S.projectiveRadicalSquareSubmodule x y) :
    e ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj y) := by
  by_contra he
  have heAmbient :
      ¬ CategoricalRadical.IsRadicalMorphism
        (S.projectiveInclusion.map e) := by
    intro heRad
    apply he
    rw [S.projectiveNilpotentRadicalData.mem_ideal_iff]
    exact (isRadicalMorphism_iff_map_of_fullyFaithful
      S.projectiveInclusion
      (CategoryTheory.fullyFaithfulInducedFunctor _) e).2 heRad
  letI : IsLocalRing (End (S.fgObj y.label)) :=
    S.fgObj_end_isLocalRing y.label
  have heSplitAmbient : IsSplitEpi (S.projectiveInclusion.map e) := by
    by_contra hsplit
    exact heAmbient
      ((MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
        (S.fgObj_indecomposable y.label).1 _).2 hsplit)
  letI : IsSplitEpi (S.projectiveInclusion.map e) := heSplitAmbient
  letI : S.projectiveInclusion.Full :=
    (CategoryTheory.fullyFaithfulInducedFunctor _).full
  letI : S.projectiveInclusion.Faithful :=
    (CategoryTheory.fullyFaithfulInducedFunctor _).faithful
  have heSplit : IsSplitEpi e := by
    apply IsSplitEpi.mk'
    refine ⟨S.projectiveInclusion.preimage
      (section_ (S.projectiveInclusion.map e)), ?_⟩
    apply S.projectiveInclusion.map_injective
    rw [S.projectiveInclusion.map_comp,
      S.projectiveInclusion.map_preimage,
      IsSplitEpi.id]
    exact (S.projectiveInclusion.map_id _).symm
  letI : IsSplitEpi e := heSplit
  apply D.hom_not_mem_radicalSquare a
  have hcancel :=
    (S.projectiveNilpotentRadicalData.ideal.pow 2).precomp
      (section_ e) hcomp
  change D.hom a ∈
    (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _
  simpa only [← Category.assoc, IsSplitEpi.id, Category.id_comp] using hcancel

/-- Perturb every arrow representative by an element of the internal
projective radical square.  This is exactly the freedom available when
changing lifts of the fixed ordinary-arrow classes. -/
def perturb (D : S.OrdinaryArrowRepresentatives)
    (r : ∀ {x y : S.ProjectiveLabel} (_ : S.OrdinaryArrow x y),
      S.projectiveRadicalSquareSubmodule x y) :
    S.OrdinaryArrowRepresentatives where
  representative := fun {x y} a ↦
    ⟨D.hom a + (r a).1,
      AddSubgroup.add_mem _ (D.hom_mem_radical a)
        (S.projectiveRadicalSquare_le_radical x y (r a).2)⟩
  representative_mkQ := by
    intro x y a
    rw [← D.representative_mkQ a]
    apply (Submodule.Quotient.eq
      (S.projectiveRadicalSquareInRadicalSubmodule x y)).2
    change
      ((⟨D.hom a + (r a).1,
          AddSubgroup.add_mem _ (D.hom_mem_radical a)
            (S.projectiveRadicalSquare_le_radical x y (r a).2)⟩ :
          S.projectiveRadicalSubmodule x y) - D.representative a).1 ∈
        S.projectiveRadicalSquareSubmodule x y
    simp [hom]

@[simp]
theorem perturb_hom (D : S.OrdinaryArrowRepresentatives)
    (r : ∀ {x y : S.ProjectiveLabel} (_ : S.OrdinaryArrow x y),
      S.projectiveRadicalSquareSubmodule x y)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    (D.perturb r).hom a = D.hom a + (r a).1 :=
  rfl

/-- Include the irreducible quotient into the full projective Hom-space
modulo the internal projective radical square. -/
def irrToHomModSquare
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (x y : S.ProjectiveLabel) :
    S.projectiveIrreducibleHomSpace x y →ₗ[k]
      ((S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) ⧸
        S.projectiveRadicalSquareSubmodule x y) :=
  (S.projectiveRadicalSquareInRadicalSubmodule x y).mapQ
    (S.projectiveRadicalSquareSubmodule x y)
    (S.projectiveRadicalSubmodule x y).subtype
    (by
      intro f hf
      exact hf)

theorem irrToHomModSquare_injective
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (x y : S.ProjectiveLabel) :
    Function.Injective (irrToHomModSquare S x y) := by
  apply LinearMap.ker_eq_bot.mp
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  induction f using Submodule.Quotient.induction_on with
  | _ f =>
      rw [irrToHomModSquare, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
      rfl

@[simp]
theorem irrToHomModSquare_arrowClass
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    irrToHomModSquare S x y (S.ordinaryArrowClass a) =
      (S.projectiveRadicalSquareSubmodule x y).mkQ (D.hom a) := by
  rw [← D.representative_mkQ a]
  rfl

/-- Any representatives of the displayed arrows remain linearly independent
in the full projective Hom-space modulo its radical square. -/
theorem homModSquare_linearIndependent
    (D : S.OrdinaryArrowRepresentatives) (x y : S.ProjectiveLabel) :
    LinearIndependent k
      (fun a : S.OrdinaryArrow x y ↦
        (S.projectiveRadicalSquareSubmodule x y).mkQ (D.hom a)) := by
  have h := (S.ordinaryArrowClass_linearIndependent x y).map'
    (irrToHomModSquare S x y)
    (LinearMap.ker_eq_bot.mpr (irrToHomModSquare_injective S x y))
  rw [show
      irrToHomModSquare S x y ∘
          (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowClass a) =
        (fun a : S.OrdinaryArrow x y ↦
          (S.projectiveRadicalSquareSubmodule x y).mkQ (D.hom a)) by
      funext a
      exact D.irrToHomModSquare_arrowClass a] at h
  exact h

/-- The identity class is not spanned by loop-arrow representatives modulo
the internal projective radical square. -/
theorem identityModSquare_not_mem_span_hom
    (D : S.OrdinaryArrowRepresentatives) (x : S.ProjectiveLabel) :
    (S.projectiveRadicalSquareSubmodule x x).mkQ
        (𝟙 (S.ordinaryProjectiveObj x)) ∉
      Submodule.span k (Set.range fun a : S.OrdinaryArrow x x ↦
        (S.projectiveRadicalSquareSubmodule x x).mkQ (D.hom a)) := by
  intro hid
  let Sq := S.projectiveRadicalSquareSubmodule x x
  let Rad := S.projectiveRadicalSubmodule x x
  have hSqRad : Sq ≤ Rad := S.projectiveRadicalSquare_le_radical x x
  have harrow :
      Submodule.span k (Set.range fun a : S.OrdinaryArrow x x ↦
        Sq.mkQ (D.hom a)) ≤ Rad.map Sq.mkQ := by
    apply Submodule.span_le.2
    rintro q ⟨a, rfl⟩
    apply Submodule.mem_map_of_mem
    exact D.hom_mem_radical a
  have hidImage : Sq.mkQ (𝟙 (S.ordinaryProjectiveObj x)) ∈
      Rad.map Sq.mkQ := harrow hid
  have hidRad : (𝟙 (S.ordinaryProjectiveObj x)) ∈ Rad := by
    have hidPre : (𝟙 (S.ordinaryProjectiveObj x)) ∈
        (Rad.map Sq.mkQ).comap Sq.mkQ := hidImage
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hSqRad] at hidPre
    exact hidPre
  have hidAmbient :
      CategoricalRadical.IsRadicalMorphism
        (S.projectiveInclusion.map (𝟙 (S.ordinaryProjectiveObj x))) :=
    (S.fgNilpotentRadicalData.mem_ideal_iff _).1 hidRad
  letI : IsLocalRing (End (S.fgObj x.label)) :=
    S.fgObj_end_isLocalRing x.label
  have hnot :
      ¬ IsSplitEpi
        (S.projectiveInclusion.map (𝟙 (S.ordinaryProjectiveObj x))) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
      (S.fgObj_indecomposable x.label).1 _).1 hidAmbient
  apply hnot
  rw [S.projectiveInclusion.map_id]
  infer_instance

/-- Two choices of representatives of the same displayed arrow differ by an
element of the internal projective radical square. -/
theorem hom_sub_hom_mem_radicalSquare
    (D E : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    D.hom a - E.hom a ∈
      S.projectiveRadicalSquareSubmodule x y := by
  let SqInRad := S.projectiveRadicalSquareInRadicalSubmodule x y
  have hquot : SqInRad.mkQ (D.representative a) =
      SqInRad.mkQ (E.representative a) := by
    change Submodule.Quotient.mk (D.representative a) =
      Submodule.Quotient.mk (E.representative a)
    rw [D.representative_mkQ a, E.representative_mkQ a]
  exact (Submodule.Quotient.eq SqInRad).1 hquot

/-- Evaluation of a path using a specified representative system. -/
def pathMap (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y) :
    S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x :=
  LinearPathCategory.pathMap S.ordinaryProjectiveObj
    (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ D.hom a) p

/-- A path of length `n` evaluated with any representative system belongs to
the `n`-th internal projective-radical power. -/
theorem pathMap_mem_radicalPow (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y) :
    D.pathMap p ∈
      (S.projectiveNilpotentRadicalData.ideal.pow p.length).hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) :=
  LinearPathCategory.pathMap_mem_ideal_pow
    S.ordinaryProjectiveObj
    (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ D.hom a)
    S.projectiveNilpotentRadicalData.ideal
    (fun {_ _} a ↦ D.hom_mem_radical a) p

/-- Replacing every arrow representative changes the evaluation of a path of
length `n` only in radical degree at least `n + 1`. -/
theorem pathMap_sub_pathMap_mem_radicalPow_succ
    (D E : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y) :
    D.pathMap p - E.pathMap p ∈
      (S.projectiveNilpotentRadicalData.ideal.pow (p.length + 1)).hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) := by
  induction p with
  | nil =>
      simp [pathMap]
  | cons p a ih =>
      rw [pathMap, pathMap, LinearPathCategory.pathMap_cons,
        LinearPathCategory.pathMap_cons, Quiver.Path.length_cons]
      have haDiff : D.hom a - E.hom a ∈
          (S.projectiveNilpotentRadicalData.ideal.pow 2).hom
            _ _ :=
        D.hom_sub_hom_mem_radicalSquare E a
      have hpD := D.pathMap_mem_radicalPow p
      have haE := E.hom_mem_radical a
      have hleft : (D.hom a - E.hom a) ≫ D.pathMap p ∈
          (S.projectiveNilpotentRadicalData.ideal.pow
            (p.length + 2)).hom
              _ _ := by
        have hmul := HomIdeal.comp_mem_mul haDiff hpD
        rw [← HomIdeal.pow_add] at hmul
        simpa only [Nat.add_comm] using hmul
      have hright : E.hom a ≫ (D.pathMap p - E.pathMap p) ∈
          (S.projectiveNilpotentRadicalData.ideal.pow
            (p.length + 2)).hom
              _ _ := by
        have haE' : E.hom a ∈
            (S.projectiveNilpotentRadicalData.ideal.pow 1).hom _ _ := by
          simpa only [HomIdeal.pow_one] using haE
        have hmul := HomIdeal.comp_mem_mul haE' ih
        rw [← HomIdeal.pow_add] at hmul
        simpa only [show 1 + (p.length + 1) = p.length + 2 by omega]
          using hmul
      have hadd := AddSubgroup.add_mem _ hleft hright
      have heq :
          D.hom a ≫ D.pathMap p - E.hom a ≫ E.pathMap p =
            (D.hom a - E.hom a) ≫ D.pathMap p +
              E.hom a ≫ (D.pathMap p - E.pathMap p) := by
        simp only [Preadditive.sub_comp, Preadditive.comp_sub]
        abel
      change D.hom a ≫ D.pathMap p - E.hom a ≫ E.pathMap p ∈ _
      rw [heq]
      simpa only [show p.length + 1 + 1 = p.length + 2 by omega]
        using hadd

/-- The free linear path realization determined by a representative system. -/
def realization (D : S.OrdinaryArrowRepresentatives) :
    LinearPathCategory.Category k S.ProjectiveLabel ⥤ S.ProjectiveCategory :=
  LinearPathCategory.lift S.ordinaryProjectiveObj
    (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ D.hom a)

noncomputable instance realization_additive
    (D : S.OrdinaryArrowRepresentatives) : D.realization.Additive := by
  dsimp only [realization]
  infer_instance

noncomputable instance realization_linear
    (D : S.OrdinaryArrowRepresentatives) : D.realization.Linear k := by
  dsimp only [realization]
  infer_instance

@[simp]
theorem realization_map_pathHom (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y) :
    D.realization.map (LinearPathCategory.pathHom p) = D.pathMap p :=
  LinearPathCategory.lift_map_pathHom
    S.ordinaryProjectiveObj
    (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ D.hom a) p

/-- The exact kernel relation family attached to a representative system. -/
def relations (D : S.OrdinaryArrowRepresentatives) :
    BoundQuiver.RelationFamily k S.ProjectiveLabel :=
  fun _ _ ↦ {f | D.realization.map f = 0}

@[simp]
theorem mem_relations_iff (D : S.OrdinaryArrowRepresentatives)
    {X Y : LinearPathCategory.Category k S.ProjectiveLabel} (f : X ⟶ Y) :
    f ∈ D.relations X Y ↔ D.realization.map f = 0 :=
  Iff.rfl

/-- The generated ideal of the kernel relation family is the pointwise
linear kernel of the realization. -/
theorem relations_generatedHomSubmodule_eq_ker
    (D : S.OrdinaryArrowRepresentatives)
    (X Y : LinearPathCategory.Category k S.ProjectiveLabel) :
    HomIdeal.generatedHomSubmodule k D.relations X Y =
      LinearMap.ker (D.realization.mapLinearMap k) := by
  ext f
  constructor
  · intro hf
    have hf' : f ∈ (HomIdeal.linearSpan k D.relations).hom X Y := hf
    have hk := HomIdeal.linearSpan_le D.relations
      (HomIdeal.functorKernel (k := k) D.realization)
      (fun hr ↦ hr) hf'
    exact hk
  · intro hf
    apply HomIdeal.relation_mem_linearSpan D.relations
    exact hf

/-- Nilpotence kills all sufficiently long paths for every choice of arrow
representatives. -/
theorem exists_realization_pathHom_eq_zero
    (D : S.OrdinaryArrowRepresentatives) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ {x y : S.ProjectiveLabel} (p : Quiver.Path x y), N ≤ p.length →
        D.realization.map (LinearPathCategory.pathHom p) = 0 := by
  obtain ⟨N₀, hN₀⟩ := S.projectiveNilpotentRadicalData.nilpotent
  refine ⟨max 2 N₀, le_max_left _ _, ?_⟩
  intro x y p hp
  have hN₀le : N₀ ≤ p.length := (le_max_right 2 N₀).trans hp
  have hpath := D.pathMap_mem_radicalPow p
  have hpathN₀ : D.pathMap p ∈
      (S.projectiveNilpotentRadicalData.ideal.pow N₀).hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) :=
    (HomIdeal.pow_le_pow_of_le S.projectiveNilpotentRadicalData.ideal
      hN₀le) _ _ hpath
  rw [hN₀] at hpathN₀
  rw [D.realization_map_pathHom]
  change D.pathMap p = 0
  simpa using hpathN₀

/-- Every sufficiently long path belongs to the generated kernel ideal for
every representative system. -/
theorem relations_long_paths_mem
    (D : S.OrdinaryArrowRepresentatives) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ {x y : S.ProjectiveLabel} (p : Quiver.Path x y), N ≤ p.length →
        LinearPathCategory.pathHom p ∈
          HomIdeal.generatedHomSubmodule k D.relations
            (LinearPathCategory.obj k S.ProjectiveLabel y)
            (LinearPathCategory.obj k S.ProjectiveLabel x) := by
  obtain ⟨N, hN, hpath⟩ := D.exists_realization_pathHom_eq_zero
  refine ⟨N, hN, ?_⟩
  intro x y p hp
  rw [D.relations_generatedHomSubmodule_eq_ker]
  exact hpath p hp

/-- Short path evaluations remain linearly independent modulo the radical
square for every representative system. -/
theorem lowPathQuotient_linearIndependent
    (D : S.OrdinaryArrowRepresentatives) (x y : S.ProjectiveLabel) :
    LinearIndependent k
      (fun p : {p : Quiver.Path x y // p.length < 2} ↦
        (S.projectiveRadicalSquareSubmodule x y).mkQ (D.pathMap p.1)) := by
  classical
  let arrowFamily := fun a : S.OrdinaryArrow x y ↦
    (S.projectiveRadicalSquareSubmodule x y).mkQ (D.hom a)
  by_cases hxy : x = y
  · subst y
    let e := LinearPathCategory.optionArrowEquivLowPath x
    let idClass :=
      (S.projectiveRadicalSquareSubmodule x x).mkQ
        (𝟙 (S.ordinaryProjectiveObj x))
    have hOption : LinearIndependent k
        (fun o ↦ Option.casesOn' o idClass arrowFamily) :=
      (D.homModSquare_linearIndependent x x).option
        (D.identityModSquare_not_mem_span_hom x)
    have hLow := hOption.comp e.symm e.symm.injective
    rw [show
        (fun o ↦ Option.casesOn' o idClass arrowFamily) ∘ e.symm =
        (fun p : {p : Quiver.Path x x // p.length < 2} ↦
          (S.projectiveRadicalSquareSubmodule x x).mkQ
            (D.pathMap p.1)) by
        funext p
        change Option.casesOn' (e.symm p) idClass arrowFamily = _
        generalize ho : e.symm p = o
        have hop : e o = p := by
          rw [← ho]
          exact e.apply_symm_apply p
        cases o with
        | none =>
            have hp : p.1 = Quiver.Path.nil := by
              simpa [e, LinearPathCategory.optionArrowEquivLowPath] using
                congrArg Subtype.val hop.symm
            rw [hp, pathMap, LinearPathCategory.pathMap_nil]
            rfl
        | some a =>
            have hp : p.1 = a.toPath := by
              simpa [e, LinearPathCategory.optionArrowEquivLowPath] using
                congrArg Subtype.val hop.symm
            rw [hp, pathMap,
              show a.toPath = Quiver.Path.nil.cons a by rfl,
              LinearPathCategory.pathMap_cons,
              LinearPathCategory.pathMap_nil, Category.comp_id]
            rfl] at hLow
    exact hLow
  · let e : S.OrdinaryArrow x y ≃
        {p : Quiver.Path x y // p.length < 2} :=
      (LinearPathCategory.arrowEquivLengthOnePath x y).trans
        (LinearPathCategory.lowPathEquivLengthOnePath hxy).symm
    have hLow := (D.homModSquare_linearIndependent x y).comp
      e.symm e.symm.injective
    rw [show arrowFamily ∘ e.symm =
        (fun p : {p : Quiver.Path x y // p.length < 2} ↦
          (S.projectiveRadicalSquareSubmodule x y).mkQ
            (D.pathMap p.1)) by
        funext p
        let a := e.symm p
        have hap : e a = p := e.apply_symm_apply p
        have hp : p.1 = (show x ⟶ y from a).toPath := by
          simpa [e, LinearPathCategory.arrowEquivLengthOnePath,
            LinearPathCategory.lowPathEquivLengthOnePath] using
              congrArg Subtype.val hap.symm
        rw [hp, pathMap,
          show (show x ⟶ y from a).toPath =
            Quiver.Path.nil.cons a by rfl,
          LinearPathCategory.pathMap_cons,
          LinearPathCategory.pathMap_nil, Category.comp_id]
        rfl] at hLow
    exact hLow

/-- Paths of length at least two evaluate into the internal projective
radical square for every representative system. -/
theorem pathMap_mem_radicalSquare
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y)
    (hp : 2 ≤ p.length) :
    D.pathMap p ∈ S.projectiveRadicalSquareSubmodule x y :=
  (HomIdeal.pow_le_pow_of_le S.projectiveNilpotentRadicalData.ideal hp)
    _ _ (D.pathMap_mem_radicalPow p)

/-- The kernel of any representative-system realization has no terms of
path length below two. -/
theorem relations_generatedHomSubmodule_le_lengthTail_two
    (D : S.OrdinaryArrowRepresentatives)
    (X Y : LinearPathCategory.Category k S.ProjectiveLabel) :
    HomIdeal.generatedHomSubmodule k D.relations X Y ≤
      LinearPathCategory.lengthTail X Y 2 := by
  intro f hf
  rw [D.relations_generatedHomSubmodule_eq_ker] at hf
  apply LinearPathCategory.mem_lengthTail_of_map_eq_zero_of_low_independent
    S.ordinaryProjectiveObj
    (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ D.hom a)
    (S.projectiveRadicalSquareSubmodule
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X))
    2
  · intro p hp
    exact D.pathMap_mem_radicalSquare p hp
  · exact D.lowPathQuotient_linearIndependent
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)
  · exact hf

/-- Every choice of representatives of the fixed ordinary arrows has an
admissible exact kernel. -/
theorem relations_isAdmissible (D : S.OrdinaryArrowRepresentatives) :
    BoundQuiver.IsAdmissible D.relations where
  relationIdeal_le_lengthTail_two :=
    D.relations_generatedHomSubmodule_le_lengthTail_two
  long_paths_mem := D.relations_long_paths_mem

end OrdinaryArrowRepresentatives

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
