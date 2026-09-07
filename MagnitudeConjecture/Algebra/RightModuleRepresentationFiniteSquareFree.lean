import MagnitudeConjecture.Algebra.RightModuleStandardFormArrowRealization
import MagnitudeConjecture.Algebra.RightModulePrimitiveDeletion
import MagnitudeConjecture.CategoryTheory.IrreducibleAbelian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Square-freeness of a representation-finite module category

Riedtmann, Section 3.5, proves that over an algebraically closed field the
irreducible quotient between two indecomposable modules of a
representation-finite algebra has dimension at most one.  The proof uses two
facts already available here: irreducible maps are monic or epic, and an
almost-split mesh containing two copies of one indecomposable forces strict
dimension growth after translation.

Rather than construct an infinite alternating translation chain, we choose a
multiple-arrow pair of maximal endpoint dimension.  The Riedtmann step
produces another multiple-arrow pair with strictly larger endpoint dimension,
which is impossible because the selected indecomposable skeleton is finite.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Coefficient-field dimension of one selected indecomposable module. -/
def objectFinrank (x : Fin S.n) : ℕ :=
  Module.finrank k (S.fgObj x)

/-- Restrict a morphism of finitely generated right modules to a `k`-linear
map on the same underlying function. -/
def homRestrictScalars {X Y : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y) : X →ₗ[k] Y :=
  f.hom.hom.restrictScalars k

@[simp]
theorem homRestrictScalars_apply
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) (x : X) :
    homRestrictScalars (k := k) f x = f.hom.hom x :=
  rfl

/-- A monic irreducible map between selected indecomposables strictly raises
coefficient-field dimension. -/
theorem objectFinrank_lt_of_irreducible_mono
    {x y : Fin S.n} (f : S.fgObj x ⟶ S.fgObj y)
    (hf : IsIrreducibleMorphism f) [Mono f] :
    S.objectFinrank x < S.objectFinrank y := by
  letI : Module.Finite k (S.fgObj x) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj x)
  letI : Module.Finite k (S.fgObj y) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj y)
  let fₖ := homRestrictScalars (k := k) f
  have hinj : Function.Injective fₖ := by
    exact (IndecomposableSkeleton.fg_mono_iff_injective f).1 inferInstance
  have hle : S.objectFinrank x ≤ S.objectFinrank y := by
    exact fₖ.finrank_le_finrank_of_injective hinj
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hsurj : Function.Surjective fₖ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
  have hsurj' : Function.Surjective f.hom.hom := hsurj
  letI : Epi f :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).2 hsurj'
  letI : IsIso f := isIso_of_mono_of_epi f
  exact hf.not_isSplitMono inferInstance

/-- An epic irreducible map between selected indecomposables strictly lowers
coefficient-field dimension. -/
theorem objectFinrank_lt_of_irreducible_epi
    {x y : Fin S.n} (f : S.fgObj x ⟶ S.fgObj y)
    (hf : IsIrreducibleMorphism f) [Epi f] :
    S.objectFinrank y < S.objectFinrank x := by
  letI : Module.Finite k (S.fgObj x) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj x)
  letI : Module.Finite k (S.fgObj y) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj y)
  let fₖ := homRestrictScalars (k := k) f
  have hsurj : Function.Surjective fₖ := by
    exact (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance
  have hle : S.objectFinrank y ≤ S.objectFinrank x := by
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hinj : Function.Injective fₖ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm).2 hsurj
  have hinj' : Function.Injective f.hom.hom := hinj
  letI : Mono f :=
    (IndecomposableSkeleton.fg_mono_iff_injective f).2 hinj'
  letI : IsIso f := isIso_of_mono_of_epi f
  exact hf.not_isSplitEpi inferInstance

/-- Inclusion of the occurrence represented by one standard-form arrow into
the chosen right-mesh middle term. -/
def standardFormOccurrenceInclusion {x y : Fin S.n}
    (a : S.StandardFormArrow x y) :
    S.fgObj y ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj x)).X₂ := by
  let i := S.standardFormArrowOccurrenceEquiv x y a
  exact eqToHom (congrArg S.fgObj i.2.symm) ≫
    FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData x i.1

/-- Projection from the chosen right-mesh middle term onto one represented
standard-form occurrence. -/
def standardFormOccurrenceProjection {x y : Fin S.n}
    (a : S.StandardFormArrow x y) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj x)).X₂ ⟶
      S.fgObj y := by
  let i := S.standardFormArrowOccurrenceEquiv x y a
  exact FiniteTauMatrix.rightMiddleProjection
      S.finiteTauCategoryData x i.1 ≫
    eqToHom (congrArg S.fgObj i.2)

@[reassoc (attr := simp)]
theorem standardFormOccurrenceInclusion_projection
    {x y : Fin S.n} (a : S.StandardFormArrow x y) :
    S.standardFormOccurrenceInclusion a ≫
      S.standardFormOccurrenceProjection a = 𝟙 (S.fgObj y) := by
  let i := S.standardFormArrowOccurrenceEquiv x y a
  change (eqToHom (congrArg S.fgObj i.2.symm) ≫
      FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData x i.1) ≫
    (FiniteTauMatrix.rightMiddleProjection
        S.finiteTauCategoryData x i.1 ≫
      eqToHom (congrArg S.fgObj i.2)) = _
  erw [Category.assoc]
  erw [← Category.assoc
    (FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData x i.1)
    (FiniteTauMatrix.rightMiddleProjection
      S.finiteTauCategoryData x i.1)
    (eqToHom (congrArg S.fgObj i.2))]
  rw [FiniteTauMatrix.rightMiddleInclusion_projection]
  simp

/-- Distinct parallel standard-form arrows represent distinct middle-term
indices. -/
theorem standardFormArrowOccurrenceEquiv_fst_ne
    {x y : Fin S.n} {a b : S.StandardFormArrow x y} (hab : a ≠ b) :
    (S.standardFormArrowOccurrenceEquiv x y a).1 ≠
      (S.standardFormArrowOccurrenceEquiv x y b).1 := by
  intro h
  apply hab
  apply (S.standardFormArrowOccurrenceEquiv x y).injective
  apply Subtype.ext
  exact h

@[reassoc (attr := simp)]
theorem standardFormOccurrenceInclusion_projection_ne
    {x y : Fin S.n} {a b : S.StandardFormArrow x y} (hab : a ≠ b) :
    S.standardFormOccurrenceInclusion a ≫
      S.standardFormOccurrenceProjection b = 0 := by
  let i := S.standardFormArrowOccurrenceEquiv x y a
  let j := S.standardFormArrowOccurrenceEquiv x y b
  have hij : i.1 ≠ j.1 := S.standardFormArrowOccurrenceEquiv_fst_ne hab
  have hzero : FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData x i.1 ≫
        FiniteTauMatrix.rightMiddleProjection
          S.finiteTauCategoryData x j.1 = 0 := by
    unfold FiniteTauMatrix.rightMiddleInclusion
      FiniteTauMatrix.rightMiddleProjection
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [biproduct.ι_π_ne _ hij]
  change (eqToHom (congrArg S.fgObj i.2.symm) ≫
      FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData x i.1) ≫
    (FiniteTauMatrix.rightMiddleProjection
        S.finiteTauCategoryData x j.1 ≫
      eqToHom (congrArg S.fgObj j.2)) = _
  erw [Category.assoc]
  erw [← Category.assoc
    (FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData x i.1)
    (FiniteTauMatrix.rightMiddleProjection
      S.finiteTauCategoryData x j.1)
    (eqToHom (congrArg S.fgObj j.2))]
  rw [hzero]
  simp
  rfl

@[simp]
theorem standardFormOccurrenceProjection_apply_inclusion
    {x y : Fin S.n} (a : S.StandardFormArrow x y) (v : S.fgObj y) :
    (S.standardFormOccurrenceProjection a).hom.hom
        ((S.standardFormOccurrenceInclusion a).hom.hom v) = v := by
  change (S.standardFormOccurrenceInclusion a ≫
    S.standardFormOccurrenceProjection a).hom.hom v = v
  rw [S.standardFormOccurrenceInclusion_projection]
  rfl

@[simp]
theorem standardFormOccurrenceProjection_apply_inclusion_ne
    {x y : Fin S.n} {a b : S.StandardFormArrow x y} (hab : a ≠ b)
    (v : S.fgObj y) :
    (S.standardFormOccurrenceProjection b).hom.hom
        ((S.standardFormOccurrenceInclusion a).hom.hom v) = 0 := by
  change (S.standardFormOccurrenceInclusion a ≫
    S.standardFormOccurrenceProjection b).hom.hom v = 0
  rw [S.standardFormOccurrenceInclusion_projection_ne hab]
  rfl

/-- Two distinct occurrences of the same indecomposable define the explicit
injective coefficient-field map from two copies into the mesh middle term. -/
def duplicateOccurrenceLinearMap {x y : Fin S.n}
    (a b : S.StandardFormArrow x y) :
    (S.fgObj y × S.fgObj y) →ₗ[k]
      (S.finiteTauCategoryData.rightMesh (S.fgObj x)).X₂ :=
  (homRestrictScalars (k := k)
      (S.standardFormOccurrenceInclusion a)).comp
      (LinearMap.fst k (S.fgObj y) (S.fgObj y)) +
    (homRestrictScalars (k := k)
      (S.standardFormOccurrenceInclusion b)).comp
      (LinearMap.snd k (S.fgObj y) (S.fgObj y))

/-- The two-occurrence map is injective because the two displayed
projections recover its two coordinates. -/
theorem duplicateOccurrenceLinearMap_injective
    {x y : Fin S.n} {a b : S.StandardFormArrow x y} (hab : a ≠ b) :
    Function.Injective (S.duplicateOccurrenceLinearMap a b) := by
  intro p q hpq
  apply Prod.ext
  · have h := congrArg
      (homRestrictScalars (k := k)
        (S.standardFormOccurrenceProjection a)) hpq
    simpa [duplicateOccurrenceLinearMap, LinearMap.add_apply,
      LinearMap.comp_apply, hab, hab.symm] using h
  · have h := congrArg
      (homRestrictScalars (k := k)
        (S.standardFormOccurrenceProjection b)) hpq
    have hab0 := S.standardFormOccurrenceInclusion_projection_ne hab
    have hbb := S.standardFormOccurrenceInclusion_projection b
    simpa [duplicateOccurrenceLinearMap, LinearMap.add_apply,
      LinearMap.comp_apply, hab, hab.symm] using h

/-- If an endpoint mesh contains at least two copies of `y`, twice the
dimension of `y` is bounded by the dimension of the middle term. -/
theorem two_mul_objectFinrank_le_rightMiddle
    (x y : Fin S.n)
    (hxy : 2 ≤ FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData y x) :
    2 * S.objectFinrank y ≤
      Module.finrank k
        (S.finiteTauCategoryData.rightMesh (S.fgObj x)).X₂ := by
  letI : Module.Finite k (S.fgObj y) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj y)
  letI : Module.Finite k
      (S.finiteTauCategoryData.rightMesh (S.fgObj x)).X₂ :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  let a : S.StandardFormArrow x y :=
    ⟨0, by exact lt_of_lt_of_le (by decide) hxy⟩
  let b : S.StandardFormArrow x y :=
    ⟨1, by exact lt_of_lt_of_le (by decide) hxy⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hinj : Function.Injective
      (S.duplicateOccurrenceLinearMap a b) :=
    S.duplicateOccurrenceLinearMap_injective hab
  have hle :=
    (S.duplicateOccurrenceLinearMap a b).finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  simpa [objectFinrank, two_mul] using hle

/-- Coefficient-field dimensions are additive across the selected ambient
Auslander--Reiten sequence. -/
theorem rightMesh_finrank_eq_translation_add_endpoint
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    Module.finrank k
        (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).X₂ =
      S.objectFinrank (S.rightTranslationEquiv z).1 +
        S.objectFinrank z.1 := by
  let B := S.minimalRightAlmostSplitAt z.1
  letI : Module.Finite k (S.fgObj (S.rightTranslationEquiv z).1) :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  letI : Module.Finite k B.middle :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  letI : Module.Finite k (S.fgObj z.1) :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  let f := homRestrictScalars (k := k) (S.rightKernelMap z)
  let g := homRestrictScalars (k := k) B.map
  have hexact : Function.Exact f g := by
    change Function.Exact (S.rightKernelMap z).hom.hom B.map.hom.hom
    exact S.rightKernelMap_functionExact z
  have hinj : Function.Injective f := by
    haveI : Mono (S.rightKernelMap z) := by
      change Mono ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map)
      infer_instance
    exact (IndecomposableSkeleton.fg_mono_iff_injective
      (S.rightKernelMap z)).1 inferInstance
  have hsurj : Function.Surjective g := by
    haveI : Epi B.map :=
      IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
        S.almostSplitSkeleton B.map B.rightAlmostSplit z.2
    exact (IndecomposableSkeleton.fg_epi_iff_surjective B.map).1
      inferInstance
  have hdim := MagnitudeConjecture.CategoryTheory.finrank_middle_eq_add_of_exact
    k f g hexact hinj hsurj
  rw [show S.finiteTauCategoryData.rightMesh (S.fgObj z.1) =
      S.labelRightMesh z.1 by
    exact S.canonicalRightMesh_at_label z.1]
  rw [show S.labelRightMesh z.1 = S.nonprojectiveRightMesh z by
    simp [labelRightMesh, z.2]]
  exact hdim

/-- A pair carrying at least two parallel irreducible maps produces another
such pair with strictly larger maximal endpoint dimension.  This is the
dimension-growth step in Riedtmann's square-freeness argument. -/
theorem exists_multipleArrow_pair_of_multipleArrow
    (x y : Fin S.n)
    (hxy : 2 ≤ FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x y) :
    ∃ x' y' : Fin S.n,
      2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x' y' ∧
      max (S.objectFinrank x) (S.objectFinrank y) <
        max (S.objectFinrank x') (S.objectFinrank y') := by
  classical
  let a : S.StandardFormArrow y x :=
    ⟨0, by exact lt_of_lt_of_le (by decide) hxy⟩
  let f : S.fgObj x ⟶ S.fgObj y := S.standardFormArrowMap a
  have hf : IsIrreducibleMorphism f :=
    S.standardFormArrowMap_isIrreducible a
  rcases hf.mono_or_epi with hmono | hepi
  · letI : Mono f := hmono
    have hdim : S.objectFinrank x < S.objectFinrank y :=
      S.objectFinrank_lt_of_irreducible_mono f hf
    have hx : ¬ Injective (S.fgObj x) := by
      intro hxInjective
      letI : Injective (S.fgObj x) := hxInjective
      apply hf.not_isSplitMono
      exact IsSplitMono.mk'
        { retraction := Injective.factorThru (𝟙 (S.fgObj x)) f
          id := Injective.comp_factorThru (𝟙 (S.fgObj x)) f }
    let xni : {i : Fin S.n // ¬ Injective (S.fgObj i)} := ⟨x, hx⟩
    let z := (S.rightTranslationEquiv).symm xni
    have hz : (S.rightTranslationEquiv z).1 = x := by
      exact congrArg Subtype.val
        (S.rightTranslationEquiv.apply_symm_apply xni)
    have hmultiple : 2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData y z.1 := by
      rw [← S.arrowMultiplicity_eq_inverseTranslation xni y]
      exact hxy
    have htwo := S.two_mul_objectFinrank_le_rightMiddle z.1 y hmultiple
    have hmesh := S.rightMesh_finrank_eq_translation_add_endpoint z
    rw [hmesh, hz] at htwo
    have hgrowth : S.objectFinrank y < S.objectFinrank z.1 := by
      omega
    refine ⟨y, z.1, hmultiple, ?_⟩
    simp only [Nat.max_eq_right (Nat.le_of_lt hdim),
      Nat.max_eq_right (Nat.le_of_lt hgrowth)]
    exact hgrowth
  · letI : Epi f := hepi
    have hdim : S.objectFinrank y < S.objectFinrank x :=
      S.objectFinrank_lt_of_irreducible_epi f hf
    have hy : ¬ Projective (S.fgObj y) := by
      intro hyProjective
      letI : Projective (S.fgObj y) := hyProjective
      apply hf.not_isSplitEpi
      exact IsSplitEpi.mk'
        { section_ := Projective.factorThru (𝟙 (S.fgObj y)) f
          id := Projective.factorThru_comp (𝟙 (S.fgObj y)) f }
    let ynp : {i : Fin S.n // ¬ Projective (S.fgObj i)} := ⟨y, hy⟩
    let t := S.rightTranslationEquiv ynp
    have hback : ((S.rightTranslationEquiv).symm t).1 = y := by
      exact congrArg Subtype.val
        (S.rightTranslationEquiv.symm_apply_apply ynp)
    have hmultiple : 2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData t.1 x := by
      rw [S.arrowMultiplicity_eq_inverseTranslation t x, hback]
      exact hxy
    have htwo := S.two_mul_objectFinrank_le_rightMiddle y x hxy
    have hmesh := S.rightMesh_finrank_eq_translation_add_endpoint ynp
    have htwo' : 2 * S.objectFinrank x ≤
        S.objectFinrank t.1 + S.objectFinrank y := calc
      _ ≤ Module.finrank k
          (S.finiteTauCategoryData.rightMesh (S.fgObj y)).X₂ := htwo
      _ = S.objectFinrank (S.rightTranslationEquiv ynp).1 +
          S.objectFinrank ynp.1 := hmesh
      _ = _ := rfl
    have hgrowth : S.objectFinrank x < S.objectFinrank t.1 := by
      omega
    refine ⟨t.1, x, hmultiple, ?_⟩
    simp only [Nat.max_eq_left (Nat.le_of_lt hdim),
      Nat.max_eq_left (Nat.le_of_lt hgrowth)]
    exact hgrowth

/-- Between two selected indecomposable modules of a representation-finite
algebra over an algebraically closed field, the numerical irreducible-arrow
multiplicity is at most one. -/
theorem arrowMultiplicity_le_one (x y : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x y ≤ 1 := by
  classical
  by_contra hle
  have hxy : 2 ≤ FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x y := by
    omega
  let pairs : Finset (Fin S.n × Fin S.n) :=
    Finset.univ.filter fun p ↦
      2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p.1 p.2
  have hxyMem : (x, y) ∈ pairs := by
    simp [pairs, hxy]
  obtain ⟨p, hp, hpMax⟩ := Finset.exists_max_image pairs
    (fun p ↦ max (S.objectFinrank p.1) (S.objectFinrank p.2))
    ⟨(x, y), hxyMem⟩
  have hpMultiple : 2 ≤ FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p.1 p.2 := by
    simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  obtain ⟨x', y', hmultiple, hgrowth⟩ :=
    S.exists_multipleArrow_pair_of_multipleArrow p.1 p.2 hpMultiple
  have hnewMem : (x', y') ∈ pairs := by
    simp [pairs, hmultiple]
  have hmax := hpMax (x', y') hnewMem
  exact (not_lt_of_ge hmax) hgrowth

/-- The standard-form reversed AR quiver has at most one arrow between any
ordered pair of vertices. -/
theorem standardFormArrow_subsingleton (x y : Fin S.n) :
    Subsingleton (S.StandardFormArrow x y) := by
  constructor
  intro a b
  apply Fin.ext
  have hle := S.arrowMultiplicity_le_one y x
  omega

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
